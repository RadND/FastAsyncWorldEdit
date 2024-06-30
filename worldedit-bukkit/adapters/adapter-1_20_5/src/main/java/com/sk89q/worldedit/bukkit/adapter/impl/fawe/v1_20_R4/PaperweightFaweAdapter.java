package com.sk89q.worldedit.bukkit.adapter.impl.fawe.v1_20_R4;

import com.fastasyncworldedit.bukkit.adapter.FaweAdapter;
import com.fastasyncworldedit.bukkit.adapter.NMSRelighterFactory;
import com.fastasyncworldedit.core.FaweCache;
import com.fastasyncworldedit.core.entity.LazyBaseEntity;
import com.fastasyncworldedit.core.extent.processor.lighting.RelighterFactory;
import com.fastasyncworldedit.core.queue.IBatchProcessor;
import com.fastasyncworldedit.core.queue.IChunkGet;
import com.fastasyncworldedit.core.queue.implementation.packet.ChunkPacket;
import com.fastasyncworldedit.core.util.NbtUtils;
import com.fastasyncworldedit.core.util.TaskManager;
import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableMap;
import com.mojang.serialization.Codec;
import com.sk89q.jnbt.CompoundTag;
import com.sk89q.jnbt.Tag;
import com.sk89q.worldedit.EditSession;
import com.sk89q.worldedit.blocks.BaseItemStack;
import com.sk89q.worldedit.bukkit.BukkitAdapter;
import com.sk89q.worldedit.bukkit.adapter.BukkitImplAdapter;
import com.sk89q.worldedit.bukkit.adapter.impl.fawe.v1_20_R4.nbt.PaperweightLazyCompoundTag;
import com.sk89q.worldedit.bukkit.adapter.impl.fawe.v1_20_R4.regen.PaperweightRegen;
import com.sk89q.worldedit.entity.BaseEntity;
import com.sk89q.worldedit.extent.Extent;
import com.sk89q.worldedit.internal.block.BlockStateIdAccess;
import com.sk89q.worldedit.internal.util.LogManagerCompat;
import com.sk89q.worldedit.internal.wna.WorldNativeAccess;
import com.sk89q.worldedit.math.BlockVector3;
import com.sk89q.worldedit.regions.Region;
import com.sk89q.worldedit.registry.state.BooleanProperty;
import com.sk89q.worldedit.registry.state.DirectionalProperty;
import com.sk89q.worldedit.registry.state.EnumProperty;
import com.sk89q.worldedit.registry.state.IntegerProperty;
import com.sk89q.worldedit.registry.state.Property;
import com.sk89q.worldedit.util.Direction;
import com.sk89q.worldedit.util.SideEffect;
import com.sk89q.worldedit.util.SideEffectSet;
import com.sk89q.worldedit.util.concurrency.LazyReference;
import com.sk89q.worldedit.util.formatting.text.Component;
import com.sk89q.worldedit.world.RegenOptions;
import com.sk89q.worldedit.world.biome.BiomeType;
import com.sk89q.worldedit.world.block.BaseBlock;
import com.sk89q.worldedit.world.block.BlockState;
import com.sk89q.worldedit.world.block.BlockStateHolder;
import com.sk89q.worldedit.world.block.BlockType;
import com.sk89q.worldedit.world.block.BlockTypesCache;
import com.sk89q.worldedit.world.entity.EntityType;
import com.sk89q.worldedit.world.generation.ConfiguredFeatureType;
import com.sk89q.worldedit.world.generation.StructureType;
import com.sk89q.worldedit.world.item.ItemType;
import com.sk89q.worldedit.world.registry.BlockMaterial;
import io.papermc.lib.PaperLib;
import net.minecraft.core.BlockPos;
import net.minecraft.core.Registry;
import net.minecraft.core.RegistryAccess;
import net.minecraft.core.SectionPos;
import net.minecraft.core.WritableRegistry;
import net.minecraft.core.component.DataComponentPatch;
import net.minecraft.core.registries.Registries;
import net.minecraft.nbt.NbtOps;
import net.minecraft.network.protocol.game.ClientboundLevelChunkWithLightPacket;
import net.minecraft.resources.ResourceLocation;
import net.minecraft.server.MinecraftServer;
import net.minecraft.server.dedicated.DedicatedServer;
import net.minecraft.server.level.ChunkHolder;
import net.minecraft.server.level.ServerChunkCache;
import net.minecraft.server.level.ServerLevel;
import net.minecraft.server.level.ServerPlayer;
import net.minecraft.util.StringRepresentable;
import net.minecraft.world.entity.Entity;
import net.minecraft.world.item.ItemStack;
import net.minecraft.world.level.ChunkPos;
import net.minecraft.world.level.biome.Biome;
import net.minecraft.world.level.block.Block;
import net.minecraft.world.level.block.entity.BlockEntity;
import net.minecraft.world.level.block.state.properties.BlockStateProperties;
import net.minecraft.world.level.block.state.properties.DirectionProperty;
import net.minecraft.world.level.chunk.ChunkGenerator;
import net.minecraft.world.level.chunk.LevelChunk;
import net.minecraft.world.level.levelgen.feature.ConfiguredFeature;
import net.minecraft.world.level.levelgen.structure.BoundingBox;
import net.minecraft.world.level.levelgen.structure.Structure;
import net.minecraft.world.level.levelgen.structure.StructureStart;
import org.apache.logging.log4j.Logger;
import org.bukkit.Bukkit;
import org.bukkit.Location;
import org.bukkit.NamespacedKey;
import org.bukkit.World;
import org.bukkit.block.data.BlockData;
import org.bukkit.craftbukkit.CraftServer;
import org.bukkit.craftbukkit.CraftWorld;
import org.bukkit.craftbukkit.block.CraftBlockState;
import org.bukkit.craftbukkit.block.data.CraftBlockData;
import org.bukkit.craftbukkit.entity.CraftEntity;
import org.bukkit.craftbukkit.entity.CraftPlayer;
import org.bukkit.craftbukkit.inventory.CraftItemStack;
import org.bukkit.craftbukkit.util.CraftNamespacedKey;
import org.bukkit.entity.Player;
import org.enginehub.linbus.tree.LinCompoundTag;
import org.enginehub.linbus.tree.LinStringTag;
import org.enginehub.linbus.tree.LinTag;

import javax.annotation.Nullable;
import java.lang.ref.WeakReference;
import java.lang.reflect.Field;
import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Locale;
import java.util.Map;
import java.util.Objects;
import java.util.OptionalInt;
import java.util.Set;
import java.util.function.Supplier;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import static net.minecraft.core.registries.Registries.BIOME;

public final class PaperweightFaweAdapter extends FaweAdapter<net.minecraft.nbt.Tag, ServerLevel> {

    private static final Logger LOGGER = LogManagerCompat.getLogger();
    private static Method CHUNK_HOLDER_WAS_ACCESSIBLE_SINCE_LAST_SAVE;
    private static final Codec<DataComponentPatch> COMPONENTS_CODEC = DataComponentPatch.CODEC.optionalFieldOf(
            "components", DataComponentPatch.EMPTY
    ).codec();

    static {
        try {
            CHUNK_HOLDER_WAS_ACCESSIBLE_SINCE_LAST_SAVE = ChunkHolder.class.getDeclaredMethod("wasAccessibleSinceLastSave");
        } catch (NoSuchMethodException ignored) { // may not be present in newer paper versions
        }
    }

    private final com.sk89q.worldedit.bukkit.adapter.ext.fawe.v1_20_R4.PaperweightAdapter parent;
    // ------------------------------------------------------------------------
    // Code that may break between versions of Minecraft
    // ------------------------------------------------------------------------
    private final PaperweightMapChunkUtil mapUtil = new PaperweightMapChunkUtil();
    private char[] ibdToStateOrdinal = null;
    private int[] ordinalToIbdID = null;
    private boolean initialised = false;
    private Map<String, List<Property<?>>> allBlockProperties = null;

    public PaperweightFaweAdapter() throws NoSuchFieldException, NoSuchMethodException {
        this.parent = new com.sk89q.worldedit.bukkit.adapter.ext.fawe.v1_20_R4.PaperweightAdapter();
    }

    @Nullable
    private static String getEntityId(Entity entity) {
        ResourceLocation resourceLocation = net.minecraft.world.entity.EntityType.getKey(entity.getType());
        return resourceLocation == null ? null : resourceLocation.toString();
    }

    private static void readEntityIntoTag(Entity entity, net.minecraft.nbt.CompoundTag compoundTag) {
        entity.save(compoundTag);
    }

    @Override
    public BukkitImplAdapter<net.minecraft.nbt.Tag> getParent() {
        return parent;
    }

    private synchronized boolean init() {
        if (ibdToStateOrdinal != null && ibdToStateOrdinal[1] != 0) {
            return false;
        }
        ibdToStateOrdinal = new char[BlockTypesCache.states.length]; // size
        ordinalToIbdID = new int[ibdToStateOrdinal.length]; // size
        for (int i = 0; i < ibdToStateOrdinal.length; i++) {
            BlockState blockState = BlockTypesCache.states[i];
            PaperweightBlockMaterial material = (PaperweightBlockMaterial) blockState.getMaterial();
            int id = Block.BLOCK_STATE_REGISTRY.getId(material.getState());
            char ordinal = blockState.getOrdinalChar();
            ibdToStateOrdinal[id] = ordinal;
            ordinalToIbdID[ordinal] = id;
        }
        Map<String, List<Property<?>>> properties = new HashMap<>();
        try {
            for (Field field : BlockStateProperties.class.getDeclaredFields()) {
                Object obj = field.get(null);
                if (!(obj instanceof net.minecraft.world.level.block.state.properties.Property<?> state)) {
                    continue;
                }
                Property<?> property;
                if (state instanceof net.minecraft.world.level.block.state.properties.BooleanProperty) {
                    property = new BooleanProperty(
                            state.getName(),
                            (List<Boolean>) ImmutableList.copyOf(state.getPossibleValues())
                    );
                } else if (state instanceof DirectionProperty) {
                    property = new DirectionalProperty(
                            state.getName(),
                            state
                                    .getPossibleValues()
                                    .stream()
                                    .map(e -> Direction.valueOf(((StringRepresentable) e).getSerializedName().toUpperCase()))
                                    .collect(Collectors.toList())
                    );
                } else if (state instanceof net.minecraft.world.level.block.state.properties.EnumProperty) {
                    property = new EnumProperty(
                            state.getName(),
                            state
                                    .getPossibleValues()
                                    .stream()
                                    .map(e -> ((StringRepresentable) e).getSerializedName())
                                    .collect(Collectors.toList())
                    );
                } else if (state instanceof net.minecraft.world.level.block.state.properties.IntegerProperty) {
                    property = new IntegerProperty(
                            state.getName(),
                            (List<Integer>) ImmutableList.copyOf(state.getPossibleValues())
                    );
                } else {
                    throw new IllegalArgumentException("FastAsyncWorldEdit needs an update to support " + state
                            .getClass()
                            .getSimpleName());
                }
                properties.compute(property.getName().toLowerCase(Locale.ROOT), (k, v) -> {
                    if (v == null) {
                        v = new ArrayList<>(Collections.singletonList(property));
                    } else {
                        v.add(property);
                    }
                    return v;
                });
            }
        } catch (IllegalAccessException e) {
            e.printStackTrace();
        } finally {
            allBlockProperties = ImmutableMap.copyOf(properties);
        }
        initialised = true;
        return true;
    }

    @Override
    public BlockMaterial getMaterial(BlockType blockType) {
        Block block = getBlock(blockType);
        return new PaperweightBlockMaterial(block);
    }

    @Override
    public synchronized BlockMaterial getMaterial(BlockState state) {
        net.minecraft.world.level.block.state.BlockState blockState = ((CraftBlockData) Bukkit.createBlockData(state.getAsString())).getState();
        return new PaperweightBlockMaterial(blockState.getBlock(), blockState);
    }

    public Block getBlock(BlockType blockType) {
        return DedicatedServer.getServer().registryAccess().registryOrThrow(Registries.BLOCK)
                .get(new ResourceLocation(blockType.getNamespace(), blockType.getResource()));
    }

    @Deprecated
    @Override
    public BlockState getBlock(Location location) {
        Preconditions.checkNotNull(location);

        int x = location.getBlockX();
        int y = location.getBlockY();
        int z = location.getBlockZ();
        final ServerLevel handle = getServerLevel(location.getWorld());
        LevelChunk chunk = handle.getChunk(x >> 4, z >> 4);
        final BlockPos blockPos = new BlockPos(x, y, z);
        final net.minecraft.world.level.block.state.BlockState blockData = chunk.getBlockState(blockPos);
        BlockState state = adapt(blockData);
        if (state == null) {
            org.bukkit.block.Block bukkitBlock = location.getBlock();
            state = BukkitAdapter.adapt(bukkitBlock.getBlockData());
        }
        return state;
    }

    @Override
    public BaseBlock getFullBlock(final Location location) {
        Preconditions.checkNotNull(location);

        int x = location.getBlockX();
        int y = location.getBlockY();
        int z = location.getBlockZ();

        final ServerLevel handle = getServerLevel(location.getWorld());
        LevelChunk chunk = handle.getChunk(x >> 4, z >> 4);
        final BlockPos blockPos = new BlockPos(x, y, z);
        final net.minecraft.world.level.block.state.BlockState blockData = chunk.getBlockState(blockPos);
        BlockState state = adapt(blockData);
        if (state == null) {
            org.bukkit.block.Block bukkitBlock = location.getBlock();
            state = BukkitAdapter.adapt(bukkitBlock.getBlockData());
        }
        if (state.getBlockType().getMaterial().hasContainer()) {

            // Read the NBT data
            BlockEntity blockEntity = chunk.getBlockEntity(blockPos, LevelChunk.EntityCreationType.CHECK);
            if (blockEntity != null) {
                net.minecraft.nbt.CompoundTag tag = blockEntity.saveWithId(DedicatedServer.getServer().registryAccess());
                return state.toBaseBlock((LinCompoundTag) toNativeLin(tag));
            }
        }

        return state.toBaseBlock();
    }

    @Override
    public Set<SideEffect> getSupportedSideEffects() {
        return SideEffectSet.defaults().getSideEffectsToApply();
    }

    @Override
    public WorldNativeAccess<?, ?, ?> createWorldNativeAccess(World world) {
        return new PaperweightFaweWorldNativeAccess(this, new WeakReference<>(getServerLevel(world)));
    }

    @Override
    public BaseEntity getEntity(org.bukkit.entity.Entity entity) {
        Preconditions.checkNotNull(entity);

        CraftEntity craftEntity = ((CraftEntity) entity);
        Entity mcEntity = craftEntity.getHandle();

        String id = getEntityId(mcEntity);

        if (id != null) {
            EntityType type = com.sk89q.worldedit.world.entity.EntityTypes.get(id);
            Supplier<LinCompoundTag> saveTag = () -> {
                final net.minecraft.nbt.CompoundTag minecraftTag = new net.minecraft.nbt.CompoundTag();
                readEntityIntoTag(mcEntity, minecraftTag);
                //add Id for AbstractChangeSet to work
                final LinCompoundTag tag = (LinCompoundTag) toNativeLin(minecraftTag);
                final Map<String, LinTag<?>> tags = NbtUtils.getLinCompoundTagValues(tag);
                tags.put("Id", LinStringTag.of(id));
                return LinCompoundTag.of(tags);
            };
            return new LazyBaseEntity(type, saveTag);
        } else {
            return null;
        }
    }

    @Override
    public Component getRichBlockName(BlockType blockType) {
        return parent.getRichBlockName(blockType);
    }

    @Override
    public Component getRichItemName(ItemType itemType) {
        return parent.getRichItemName(itemType);
    }

    @Override
    public Component getRichItemName(BaseItemStack itemStack) {
        return parent.getRichItemName(itemStack);
    }

    @Override
    public OptionalInt getInternalBlockStateId(BlockState state) {
        PaperweightBlockMaterial material = (PaperweightBlockMaterial) state.getMaterial();
        net.minecraft.world.level.block.state.BlockState mcState = material.getCraftBlockData().getState();
        return OptionalInt.of(Block.BLOCK_STATE_REGISTRY.getId(mcState));
    }

    @Override
    public BlockState adapt(BlockData blockData) {
        CraftBlockData cbd = ((CraftBlockData) blockData);
        net.minecraft.world.level.block.state.BlockState ibd = cbd.getState();
        return adapt(ibd);
    }

    public BlockState adapt(net.minecraft.world.level.block.state.BlockState blockState) {
        return BlockTypesCache.states[adaptToChar(blockState)];
    }

    public char adaptToChar(net.minecraft.world.level.block.state.BlockState blockState) {
        int id = Block.BLOCK_STATE_REGISTRY.getId(blockState);
        if (initialised) {
            return ibdToStateOrdinal[id];
        }
        synchronized (this) {
            if (initialised) {
                return ibdToStateOrdinal[id];
            }
            try {
                init();
                return ibdToStateOrdinal[id];
            } catch (ArrayIndexOutOfBoundsException e1) {
                LOGGER.error("Attempted to convert {} with ID {} to char. ibdToStateOrdinal length: {}. Defaulting to air!",
                        blockState.getBlock(), Block.BLOCK_STATE_REGISTRY.getId(blockState), ibdToStateOrdinal.length, e1
                );
                return BlockTypesCache.ReservedIDs.AIR;
            }
        }
    }

    public char ibdIDToOrdinal(int id) {
        if (initialised) {
            return ibdToStateOrdinal[id];
        }
        synchronized (this) {
            if (initialised) {
                return ibdToStateOrdinal[id];
            }
            init();
            return ibdToStateOrdinal[id];
        }
    }

    @Override
    public char[] getIbdToStateOrdinal() {
        if (initialised) {
            return ibdToStateOrdinal;
        }
        synchronized (this) {
            if (initialised) {
                return ibdToStateOrdinal;
            }
            init();
            return ibdToStateOrdinal;
        }
    }

    public int ordinalToIbdID(char ordinal) {
        if (initialised) {
            return ordinalToIbdID[ordinal];
        }
        synchronized (this) {
            if (initialised) {
                return ordinalToIbdID[ordinal];
            }
            init();
            return ordinalToIbdID[ordinal];
        }
    }

    @Override
    public int[] getOrdinalToIbdID() {
        if (initialised) {
            return ordinalToIbdID;
        }
        synchronized (this) {
            if (initialised) {
                return ordinalToIbdID;
            }
            init();
            return ordinalToIbdID;
        }
    }

    @Override
    public <B extends BlockStateHolder<B>> BlockData adapt(B state) {
        PaperweightBlockMaterial material = (PaperweightBlockMaterial) state.getMaterial();
        return material.getCraftBlockData();
    }

    @Override
    public void sendFakeChunk(World world, Player player, ChunkPacket chunkPacket) {
        ServerLevel nmsWorld = getServerLevel(world);
        ChunkHolder map = PaperweightPlatformAdapter.getPlayerChunk(nmsWorld, chunkPacket.getChunkX(), chunkPacket.getChunkZ());
        if (map != null && wasAccessibleSinceLastSave(map)) {
            boolean flag = false;
            // PlayerChunk.d players = map.players;
            Stream<ServerPlayer> stream = /*players.a(new ChunkCoordIntPair(packet.getChunkX(), packet.getChunkZ()), flag)
             */ Stream.empty();

            ServerPlayer checkPlayer = player == null ? null : ((CraftPlayer) player).getHandle();
            stream.filter(entityPlayer -> checkPlayer == null || entityPlayer == checkPlayer)
                    .forEach(entityPlayer -> {
                        synchronized (chunkPacket) {
                            ClientboundLevelChunkWithLightPacket nmsPacket = (ClientboundLevelChunkWithLightPacket) chunkPacket.getNativePacket();
                            if (nmsPacket == null) {
                                nmsPacket = mapUtil.create(this, chunkPacket);
                                chunkPacket.setNativePacket(nmsPacket);
                            }
                            try {
                                FaweCache.INSTANCE.CHUNK_FLAG.get().set(true);
                                entityPlayer.connection.send(nmsPacket);
                            } finally {
                                FaweCache.INSTANCE.CHUNK_FLAG.get().set(false);
                            }
                        }
                    });
        }
    }

    @Override
    public Map<String, ? extends Property<?>> getProperties(BlockType blockType) {
        return getParent().getProperties(blockType);
    }

    @Override
    public boolean canPlaceAt(World world, BlockVector3 blockVector3, BlockState blockState) {
        int internalId = BlockStateIdAccess.getBlockStateId(blockState);
        net.minecraft.world.level.block.state.BlockState blockState1 = Block.stateById(internalId);
        return blockState1.hasPostProcess(
                getServerLevel(world),
                new BlockPos(blockVector3.x(), blockVector3.y(), blockVector3.z())
        );
    }

    @Override
    public org.bukkit.inventory.ItemStack adapt(BaseItemStack baseItemStack) {
        final RegistryAccess.Frozen registryAccess = DedicatedServer.getServer().registryAccess();
        ItemStack stack = new ItemStack(
                registryAccess.registryOrThrow(Registries.ITEM).get(ResourceLocation.tryParse(baseItemStack.getType().id())),
                baseItemStack.getAmount()
        );
        final net.minecraft.nbt.CompoundTag nbt = (net.minecraft.nbt.CompoundTag) fromNative(baseItemStack.getNbtData());
        if (nbt != null) {
            final DataComponentPatch patch = COMPONENTS_CODEC
                    .parse(registryAccess.createSerializationContext(NbtOps.INSTANCE), nbt)
                    .getOrThrow();
            stack.applyComponents(patch);
        }
        return CraftItemStack.asCraftMirror(stack);
    }

    @Override
    protected void preCaptureStates(final ServerLevel serverLevel) {
        serverLevel.captureTreeGeneration = true;
        serverLevel.captureBlockStates = true;
    }

    @Override
    protected List<org.bukkit.block.BlockState> getCapturedBlockStatesCopy(final ServerLevel serverLevel) {
        return new ArrayList<>(serverLevel.capturedBlockStates.values());
    }

    @Override
    protected void postCaptureBlockStates(final ServerLevel serverLevel) {
        serverLevel.captureBlockStates = false;
        serverLevel.captureTreeGeneration = false;
        serverLevel.capturedBlockStates.clear();
    }

    @Override
    protected ServerLevel getServerLevel(final World world) {
        return ((CraftWorld) world).getHandle();
    }

    @Override
    public boolean generateFeature(ConfiguredFeatureType feature, World world, EditSession editSession, BlockVector3 pt) {
        //FAWE start
        ServerLevel serverLevel = ((CraftWorld) world).getHandle();
        ChunkGenerator generator = serverLevel.getMinecraftWorld().getChunkSource().getGenerator();

        ConfiguredFeature<?, ?> configuredFeature = serverLevel
                .registryAccess()
                .registryOrThrow(Registries.CONFIGURED_FEATURE)
                .get(ResourceLocation.tryParse(feature.id()));
        FaweBlockStateListPopulator populator = new FaweBlockStateListPopulator(serverLevel);

        Map<BlockPos, CraftBlockState> placed = TaskManager.taskManager().sync(() -> {
            serverLevel.captureTreeGeneration = true;
            serverLevel.captureBlockStates = true;
            try {
                if (!configuredFeature.place(
                        populator,
                        generator,
                        serverLevel.random,
                        new BlockPos(pt.x(), pt.y(), pt.z())
                )) {
                    return null;
                }
                Map<BlockPos, CraftBlockState> placedBlocks = populator.getList().stream().collect(Collectors.toMap(
                        CraftBlockState::getPosition,
                        craftBlockState -> craftBlockState
                ));
                placedBlocks.putAll(serverLevel.capturedBlockStates);
                return placedBlocks;
            } finally {
                serverLevel.captureBlockStates = false;
                serverLevel.captureTreeGeneration = false;
                serverLevel.capturedBlockStates.clear();
            }
        });

        return placeFeatureIntoSession(editSession, populator, placed);
        //FAWE end
    }

    @Override
    public boolean generateStructure(StructureType type, World world, EditSession editSession, BlockVector3 pt) {
        ServerLevel serverLevel = ((CraftWorld) world).getHandle();
        Structure k = serverLevel
                .registryAccess()
                .registryOrThrow(Registries.STRUCTURE)
                .get(ResourceLocation.tryParse(type.id()));
        if (k == null) {
            return false;
        }

        ServerChunkCache chunkManager = serverLevel.getChunkSource();

        ChunkPos chunkPos = new ChunkPos(new BlockPos(pt.x(), pt.y(), pt.z()));

        //FAWE start
        FaweBlockStateListPopulator populator = new FaweBlockStateListPopulator(serverLevel);
        Map<BlockPos, CraftBlockState> placed = TaskManager.taskManager().sync(() -> {
            serverLevel.captureTreeGeneration = true;
            serverLevel.captureBlockStates = true;
            try {
                StructureStart structureStart = k.generate(
                        serverLevel.registryAccess(),
                        chunkManager.getGenerator(),
                        chunkManager.getGenerator().getBiomeSource(),
                        chunkManager.randomState(),
                        serverLevel.getStructureManager(),
                        serverLevel.getSeed(),
                        chunkPos,
                        0,
                        populator,
                        biome -> true
                );
                if (!structureStart.isValid()) {
                    return null;
                } else {
                    BoundingBox boundingBox = structureStart.getBoundingBox();
                    ChunkPos min = new ChunkPos(
                            SectionPos.blockToSectionCoord(boundingBox.minX()),
                            SectionPos.blockToSectionCoord(boundingBox.minZ())
                    );
                    ChunkPos max = new ChunkPos(
                            SectionPos.blockToSectionCoord(boundingBox.maxX()),
                            SectionPos.blockToSectionCoord(boundingBox.maxZ())
                    );
                    ChunkPos.rangeClosed(min, max).forEach((chunkPosx) -> structureStart.placeInChunk(
                            populator,
                            serverLevel.structureManager(),
                            chunkManager.getGenerator(),
                            serverLevel.getRandom(),
                            new BoundingBox(
                                    chunkPosx.getMinBlockX(),
                                    serverLevel.getMinBuildHeight(),
                                    chunkPosx.getMinBlockZ(),
                                    chunkPosx.getMaxBlockX(),
                                    serverLevel.getMaxBuildHeight(),
                                    chunkPosx.getMaxBlockZ()
                            ),
                            chunkPosx
                    ));
                    Map<BlockPos, CraftBlockState> placedBlocks = populator.getList().stream().collect(Collectors.toMap(
                            CraftBlockState::getPosition,
                            craftBlockState -> craftBlockState
                    ));
                    placedBlocks.putAll(serverLevel.capturedBlockStates);
                    return placedBlocks;
                }
            } finally {
                serverLevel.captureBlockStates = false;
                serverLevel.captureTreeGeneration = false;
                serverLevel.capturedBlockStates.clear();
            }
        });

        return placeFeatureIntoSession(editSession, populator, placed);
        //FAWE end
    }

    private boolean placeFeatureIntoSession(
            final EditSession editSession,
            final FaweBlockStateListPopulator populator,
            final Map<BlockPos, CraftBlockState> placed
    ) {
        if (placed == null || placed.isEmpty()) {
            return false;
        }

        for (Map.Entry<BlockPos, CraftBlockState> entry : placed.entrySet()) {
            CraftBlockState craftBlockState = entry.getValue();
            if (entry.getValue() == null) {
                continue;
            }
            BlockPos pos = entry.getKey();
            editSession.setBlock(pos.getX(), pos.getY(), pos.getZ(), BukkitAdapter.adapt(craftBlockState.getBlockData()));
            BlockEntity blockEntity = populator.getBlockEntity(pos);
            if (blockEntity != null) {
                net.minecraft.nbt.CompoundTag tag = blockEntity.saveWithId(DedicatedServer.getServer().registryAccess());
                editSession.setTile(pos.getX(), pos.getY(), pos.getZ(), (CompoundTag) toNative(tag));
            }
        }
        return true;
    }

    @Override
    public void setupFeatures() {
        DedicatedServer server = ((CraftServer) Bukkit.getServer()).getServer();

        // Features
        for (ResourceLocation name : server.registryAccess().registryOrThrow(Registries.CONFIGURED_FEATURE).keySet()) {
            if (ConfiguredFeatureType.REGISTRY.get(name.toString()) == null) {
                ConfiguredFeatureType.REGISTRY.register(name.toString(), new ConfiguredFeatureType(name.toString()));
            }
        }

        // Structures
        for (ResourceLocation name : server.registryAccess().registryOrThrow(Registries.STRUCTURE).keySet()) {
            if (StructureType.REGISTRY.get(name.toString()) == null) {
                StructureType.REGISTRY.register(name.toString(), new StructureType(name.toString()));
            }
        }
    }

    @Override
    public BaseItemStack adapt(org.bukkit.inventory.ItemStack itemStack) {
        final RegistryAccess.Frozen registryAccess = DedicatedServer.getServer().registryAccess();
        final ItemStack nmsStack = CraftItemStack.asNMSCopy(itemStack);
        final net.minecraft.nbt.Tag tag = COMPONENTS_CODEC.encodeStart(
                registryAccess.createSerializationContext(NbtOps.INSTANCE),
                nmsStack.getComponentsPatch()
        ).getOrThrow();
        return new BaseItemStack(
                BukkitAdapter.asItemType(itemStack.getType()),
                LazyReference.from(() -> (LinCompoundTag) toNativeLin(tag)),
                itemStack.getAmount()
        );
    }

    @Override
    public Tag toNative(net.minecraft.nbt.Tag foreign) {
        return parent.toNative(foreign);
    }

    @Override
    public net.minecraft.nbt.Tag fromNative(Tag foreign) {
        if (foreign instanceof PaperweightLazyCompoundTag) {
            return ((PaperweightLazyCompoundTag) foreign).get();
        }
        return parent.fromNative(foreign);
    }

    @Override
    public boolean regenerate(World bukkitWorld, Region region, Extent target, RegenOptions options) throws Exception {
        return new PaperweightRegen(bukkitWorld, region, target, options).regenerate();
    }

    @Override
    public IChunkGet get(World world, int chunkX, int chunkZ) {
        return new PaperweightGetBlocks(world, chunkX, chunkZ);
    }

    @Override
    public int getInternalBiomeId(BiomeType biomeType) {
        final Registry<Biome> registry = MinecraftServer
                .getServer()
                .registryAccess()
                .registryOrThrow(BIOME);
        ResourceLocation resourceLocation = ResourceLocation.tryParse(biomeType.id());
        Biome biome = registry.get(resourceLocation);
        return registry.getId(biome);
    }

    @Override
    public Iterable<NamespacedKey> getRegisteredBiomes() {
        WritableRegistry<Biome> biomeRegistry = (WritableRegistry<Biome>) ((CraftServer) Bukkit.getServer())
                .getServer()
                .registryAccess()
                .registryOrThrow(BIOME);
        List<ResourceLocation> keys = biomeRegistry.stream()
                .map(biomeRegistry::getKey).filter(Objects::nonNull).toList();
        List<NamespacedKey> namespacedKeys = new ArrayList<>();
        for (ResourceLocation key : keys) {
            try {
                namespacedKeys.add(CraftNamespacedKey.fromMinecraft(key));
            } catch (IllegalArgumentException e) {
                LOGGER.error("Error converting biome key {}", key.toString(), e);
            }
        }
        return namespacedKeys;
    }

    @Override
    public RelighterFactory getRelighterFactory() {
        if (PaperLib.isPaper()) {
            return new PaperweightStarlightRelighterFactory();
        } else {
            return new NMSRelighterFactory();
        }
    }

    @Override
    public Map<String, List<Property<?>>> getAllProperties() {
        if (initialised) {
            return allBlockProperties;
        }
        synchronized (this) {
            if (initialised) {
                return allBlockProperties;
            }
            init();
            return allBlockProperties;
        }
    }

    @Override
    public IBatchProcessor getTickingPostProcessor() {
        return new PaperweightPostProcessor();
    }

    private boolean wasAccessibleSinceLastSave(ChunkHolder holder) {
        if (!PaperLib.isPaper() || !PaperweightPlatformAdapter.POST_CHUNK_REWRITE) {
            try {
                return (boolean) CHUNK_HOLDER_WAS_ACCESSIBLE_SINCE_LAST_SAVE.invoke(holder);
            } catch (IllegalAccessException | InvocationTargetException ignored) {
                // fall-through
            }
        }
        // Papers new chunk system has no related replacement - therefor we assume true.
        return true;
    }

}
