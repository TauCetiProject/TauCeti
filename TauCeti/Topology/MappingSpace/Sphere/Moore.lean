/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.MappingSpace.Sphere.Circle
public import TauCeti.Topology.MappingSpace.Sphere.FreeLoop
public import TauCeti.Topology.MappingSpace.Sphere.Group
public import TauCeti.Topology.PathSpace.Moore.Comparison.Between
public import TauCeti.Topology.Sphere.Suspension

/-!
# Sphere mapping spaces and Moore path and loop spaces

Composing the fixed-interval sphere mapping-space homeomorphisms with the Moore path and loop
comparisons gives homotopy and fibre homotopy equivalences with Moore models:

* For a topological group `G`, `TauCeti.sphere2GroupHomotopyEquivMoore` identifies
  `G × Ω^M(ΩG) ≃ₕ Map(S², G)` compatibly with evaluation at the north pole.
* For a based space `(X, x)`, `TauCeti.mooreLoopSpaceHomotopyEquivBasedMapSphere1` and
  `TauCeti.mooreLoopSpaceHomotopyEquivBasedMapCircleOne` identify `MooreLoopSpace X x` with
  `BasedMap Sphere1 X Sphere1.east x` and `BasedMap Circle X 1 x`, sending `1` to the constant
  based map.
* For any space `Q`, `TauCeti.sphere2FiberHomotopyEquivMoorePaths` is a fibre homotopy equivalence
  over `Q × Q` between the Moore path space `ConstContractibleMoorePaths Q` (paths in `𝓛₀Q`
  between constant loops) and `C(Sphere2, Q)` over evaluation at the north and south poles,
  compatible with constant sections
  (`sphere2FiberHomotopyEquivMoorePaths_toFun_comp_constContractibleMooreSection`,
  `sphere2ConstMooreSectionHomotopy`).
* For a based space `(Q, x)`, `TauCeti.basedMapSphere2FiberHomotopyEquivMoorePaths` is a fibre
  homotopy equivalence over `Q` between `BasedConstContractibleMoorePaths Q x` (Moore paths in
  `𝓛₀Q` from `constContractibleLoop x` to constant loops) and `BasedMap Sphere2 Q Sphere2.north x`
  over south-pole evaluation, sending the duration-zero constant path at `x` to the constant based
  map.

## Main declarations

* `TauCeti.sphere2GroupHomotopyEquivMoore`: `G × Ω^M(ΩG) ≃ₕ Map(S², G)`.
* `TauCeti.mooreLoopSpaceHomotopyEquivBasedMapSphere1`,
  `TauCeti.mooreLoopSpaceHomotopyEquivBasedMapCircleOne`:
  `MooreLoopSpace X x ≃ₕ Map_*(S¹, X)`.
* `TauCeti.contractibleConstLoopPathHomeomorphUnitPathsBetween`,
  `TauCeti.sphere2FiberHomotopyEquivMoorePaths`, `TauCeti.sphere2HomotopyEquivMoorePaths`:
  `P_{Q→Q} 𝓛₀Q ≃ₕ Map(S², Q)` over `Q × Q`.
* `TauCeti.basedContractibleConstLoopPathHomeomorphUnitPathsBetween`,
  `TauCeti.basedMapSphere2FiberHomotopyEquivMoorePaths`,
  `TauCeti.basedMapSphere2HomotopyEquivMoorePaths`:
  `P_{⋆→Q} 𝓛₀Q ≃ₕ Map_*(S², Q)` over `Q`.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §5.2, §6.4, and §7.1.
-/

public section

noncomputable section

open scoped NNReal unitInterval ContinuousMap
open unitInterval

namespace TauCeti

section Group

variable (G : Type*) [TopologicalSpace G] [Group G] [IsTopologicalGroup G]

-- `Ω² G = (iteratedLoopSpace ⟨G, 1⟩ 2).carrier` is `Path (refl 1) (refl 1)` by the definition of
-- the iterated loop space, so the Moore comparison for the loops at `refl 1` in `ΩG` lands in it.
/-- **`Map(S², G)` is homotopy equivalent to `G × Ω^M(ΩG)`**, with `Ω^M(ΩG)` the Moore loops in
the fixed-interval loop space of `G`, based at the constant loop. -/
def sphere2GroupHomotopyEquivMoore :
    ContinuousMap.HomotopyEquiv (G × MooreLoopSpace (Path (1 : G) 1) (Path.refl 1)) C(Sphere2, G) :=
  (ContinuousMap.HomotopyEquiv.prodCongr (ContinuousMap.HomotopyEquiv.refl G)
    (MooreLoopSpace.homotopyEquivPath (Path.refl (1 : G)))).trans
      (sphereGroupHomeomorphIteratedLoopSpace 2 G Sphere2.north).toHomotopyEquiv

variable {G}

/-- The forward map of `sphere2GroupHomotopyEquivMoore` reparametrizes the Moore loop to the unit
interval and applies the decomposition `G × Ω²G ≃ₜ Map(S², G)`. -/
theorem sphere2GroupHomotopyEquivMoore_apply (g : G)
    (γ : MooreLoopSpace (Path (1 : G) 1) (Path.refl 1)) :
    sphere2GroupHomotopyEquivMoore G (g, γ) =
      sphereGroupHomeomorphIteratedLoopSpace 2 G Sphere2.north
        (g, MooreLoopSpace.homotopyEquivPath (Path.refl (1 : G)) γ) := by
  rw [sphere2GroupHomotopyEquivMoore]
  -- unfolding the composite of homotopy equivalences gives the displayed composite of maps
  rfl

/-- The value at the north pole of the image of `(g, γ)` is `g`. -/
@[simp]
theorem sphere2GroupHomotopyEquivMoore_apply_north (g : G)
    (γ : MooreLoopSpace (Path (1 : G) 1) (Path.refl 1)) :
    sphere2GroupHomotopyEquivMoore G (g, γ) Sphere2.north = g := by
  have h := sphereGroupHomeomorphIteratedLoopSpace_symm_fst (s₀ := Sphere2.north)
    (sphereGroupHomeomorphIteratedLoopSpace 2 G Sphere2.north
      (g, MooreLoopSpace.homotopyEquivPath (Path.refl (1 : G)) γ))
  rw [Homeomorph.symm_apply_apply] at h
  exact h.symm

/-- The group coordinate of the image under the homotopy inverse of `sphere2GroupHomotopyEquivMoore`
is the value at the north pole. -/
@[simp]
theorem sphere2GroupHomotopyEquivMoore_symm_apply_fst (f : C(Sphere2, G)) :
    ((sphere2GroupHomotopyEquivMoore G).symm f).1 = f Sphere2.north := by
  rw [sphere2GroupHomotopyEquivMoore]
  exact sphereGroupHomeomorphIteratedLoopSpace_symm_fst (s₀ := Sphere2.north) f

/-- The Moore-loop coordinate of the image under the homotopy inverse of
`sphere2GroupHomotopyEquivMoore` is the corresponding fixed-interval double loop, reparametrized to
a Moore loop of length one: the homotopy inverse of `MooreLoopSpace.homotopyEquivPath` is
`Path.toMooreLoop`. -/
@[simp]
theorem sphere2GroupHomotopyEquivMoore_symm_apply_snd (f : C(Sphere2, G)) :
    ((sphere2GroupHomotopyEquivMoore G).symm f).2 =
      Path.toMooreLoop ((sphereGroupHomeomorphIteratedLoopSpace 2 G Sphere2.north).symm f).2 := by
  rw [sphere2GroupHomotopyEquivMoore]
  exact MooreLoopSpace.homotopyEquivPath_symm_apply (X := Path (1 : G) 1) (x := Path.refl 1)
    ((sphereGroupHomeomorphIteratedLoopSpace 2 G Sphere2.north).symm f).2

end Group

/-! ### Based maps from the circle and Moore loops -/

section Circle

variable (X : Type*) [TopologicalSpace X] (x : X)

/-- **Based maps `(Sphere1, east) → (X, x)` are homotopy equivalent to `MooreLoopSpace X x`**,
composing `MooreLoopSpace.homotopyEquivPath` with `basedMapCircleHomeomorph.symm`. -/
def mooreLoopSpaceHomotopyEquivBasedMapSphere1 :
    MooreLoopSpace X x ≃ₕ BasedMap Sphere1 X Sphere1.east x :=
  (MooreLoopSpace.homotopyEquivPath x).trans
    (BasedTopologicalSpace.basedMapCircleHomeomorph ⟨X, x⟩).symm.toHomotopyEquiv

variable {X x}

-- `(⟨X, x⟩.iteratedLoopSpace 1).carrier` reduces to `Path x x` at default rather than `implicit`
-- transparency, so apply `HomotopyEquiv.trans_apply` / `trans_symm_apply` directly via `Eq.trans`.
theorem mooreLoopSpaceHomotopyEquivBasedMapSphere1_apply (γ : MooreLoopSpace X x) :
    mooreLoopSpaceHomotopyEquivBasedMapSphere1 X x γ =
      (BasedTopologicalSpace.basedMapCircleHomeomorph ⟨X, x⟩).symm γ.toPath := by
  rw [mooreLoopSpaceHomotopyEquivBasedMapSphere1]
  refine (ContinuousMap.HomotopyEquiv.trans_apply (MooreLoopSpace.homotopyEquivPath x)
    (BasedTopologicalSpace.basedMapCircleHomeomorph ⟨X, x⟩).symm.toHomotopyEquiv γ).trans ?_
  exact (congrFun (Homeomorph.coe_toHomotopyEquiv _) _).trans
    (congrArg (BasedTopologicalSpace.basedMapCircleHomeomorph ⟨X, x⟩).symm
      (MooreLoopSpace.homotopyEquivPath_apply γ))

@[simp]
theorem mooreLoopSpaceHomotopyEquivBasedMapSphere1_symm_apply
    (φ : BasedMap Sphere1 X Sphere1.east x) :
    (mooreLoopSpaceHomotopyEquivBasedMapSphere1 X x).symm φ =
      (BasedTopologicalSpace.basedMapCircleHomeomorph ⟨X, x⟩ φ).toMooreLoop := by
  rw [mooreLoopSpaceHomotopyEquivBasedMapSphere1]
  refine (ContinuousMap.HomotopyEquiv.trans_symm_apply (MooreLoopSpace.homotopyEquivPath x)
    (BasedTopologicalSpace.basedMapCircleHomeomorph ⟨X, x⟩).symm.toHomotopyEquiv φ).trans ?_
  have hsymm :
      (BasedTopologicalSpace.basedMapCircleHomeomorph ⟨X, x⟩).symm.toHomotopyEquiv.symm φ =
        BasedTopologicalSpace.basedMapCircleHomeomorph ⟨X, x⟩ φ := by
    rw [← Homeomorph.symm_toHomotopyEquiv, Homeomorph.symm_symm, Homeomorph.coe_toHomotopyEquiv]
  exact (congrArg (MooreLoopSpace.homotopyEquivPath x).symm hsymm).trans
    (MooreLoopSpace.homotopyEquivPath_symm_apply _)

@[simp]
theorem mooreLoopSpaceHomotopyEquivBasedMapSphere1_one :
    mooreLoopSpaceHomotopyEquivBasedMapSphere1 X x 1 = ⟨ContinuousMap.const Sphere1 x, rfl⟩ := by
  rw [mooreLoopSpaceHomotopyEquivBasedMapSphere1_apply, MooreLoopSpace.toPath_one,
    BasedTopologicalSpace.basedMapCircleHomeomorph_symm_refl ⟨X, x⟩]

variable (X x) in
/-- **Based maps `(Circle, 1) → (X, x)` are homotopy equivalent to `MooreLoopSpace X x`**,
composing `MooreLoopSpace.homotopyEquivPath` with `(basedMapCircleOneHomeomorphPath x).symm`. -/
def mooreLoopSpaceHomotopyEquivBasedMapCircleOne :
    MooreLoopSpace X x ≃ₕ BasedMap Circle X 1 x :=
  (MooreLoopSpace.homotopyEquivPath x).trans
    (basedMapCircleOneHomeomorphPath x).symm.toHomotopyEquiv

theorem mooreLoopSpaceHomotopyEquivBasedMapCircleOne_apply (γ : MooreLoopSpace X x) :
    mooreLoopSpaceHomotopyEquivBasedMapCircleOne X x γ =
      (basedMapCircleOneHomeomorphPath x).symm γ.toPath := by
  rw [mooreLoopSpaceHomotopyEquivBasedMapCircleOne, ContinuousMap.HomotopyEquiv.trans_apply,
    Homeomorph.coe_toHomotopyEquiv, MooreLoopSpace.homotopyEquivPath_apply]

@[simp]
theorem mooreLoopSpaceHomotopyEquivBasedMapCircleOne_apply_unitToCircle
    (γ : MooreLoopSpace X x) (t : I) :
    (mooreLoopSpaceHomotopyEquivBasedMapCircleOne X x γ).1 (unitToCircle t) = γ.toPath t := by
  rw [mooreLoopSpaceHomotopyEquivBasedMapCircleOne_apply,
    basedMapCircleOneHomeomorphPath_symm_unitToCircle]

@[simp]
theorem mooreLoopSpaceHomotopyEquivBasedMapCircleOne_symm_apply
    (φ : BasedMap Circle X 1 x) :
    (mooreLoopSpaceHomotopyEquivBasedMapCircleOne X x).symm φ =
      (basedMapCircleOneHomeomorphPath x φ).toMooreLoop := by
  rw [mooreLoopSpaceHomotopyEquivBasedMapCircleOne, ContinuousMap.HomotopyEquiv.trans_symm_apply,
    ← Homeomorph.symm_toHomotopyEquiv, Homeomorph.symm_symm, Homeomorph.coe_toHomotopyEquiv,
    MooreLoopSpace.homotopyEquivPath_symm_apply]

@[simp]
theorem mooreLoopSpaceHomotopyEquivBasedMapCircleOne_one :
    mooreLoopSpaceHomotopyEquivBasedMapCircleOne X x 1 = ⟨ContinuousMap.const Circle x, rfl⟩ := by
  rw [mooreLoopSpaceHomotopyEquivBasedMapCircleOne_apply, MooreLoopSpace.toPath_one,
    basedMapCircleOneHomeomorphPath_symm_refl]

end Circle

/-! ### Unbased two-sphere maps and Moore paths between constant contractible loops -/

section Sphere2

variable (Q : Type*) [TopologicalSpace Q]

/-- Moore paths in `𝓛₀Q` starting and ending at constant loops (`P_{Q→Q} 𝓛₀Q`). -/
abbrev ConstContractibleMoorePaths : Type _ :=
  MoorePath.pathsBetween (Set.range (constContractibleLoop (Q := Q)))
    (Set.range (constContractibleLoop (Q := Q)))

/-- Retract pairs of constant contractible loops to `Q × Q` via basepoint evaluation. -/
def constContractibleRangeToProd :
    C(↥(Set.range (constContractibleLoop (Q := Q))) ×
      ↥(Set.range (constContractibleLoop (Q := Q))), Q × Q) :=
  (basepointContractibleLoop.comp (ContinuousMap.subtypeVal _)).prodMap
    (basepointContractibleLoop.comp (ContinuousMap.subtypeVal _))

@[simp]
theorem constContractibleRangeToProd_apply
    (p : ↥(Set.range (constContractibleLoop (Q := Q))) ×
      ↥(Set.range (constContractibleLoop (Q := Q)))) :
    constContractibleRangeToProd Q p =
      (basepointContractibleLoop p.1.1, basepointContractibleLoop p.2.1) := by
  cases p
  simp [constContractibleRangeToProd]

/-- Endpoint evaluation `P_{Q→Q} 𝓛₀Q → Q × Q` reading the start and end constant loops in `Q`. -/
def constContractibleMooreEndpoints : C(ConstContractibleMoorePaths Q, Q × Q) :=
  (constContractibleRangeToProd Q).comp
    (MoorePath.endpointsBetween (Set.range (constContractibleLoop (Q := Q)))
      (Set.range (constContractibleLoop (Q := Q))))

@[simp]
theorem constContractibleMooreEndpoints_apply (γ : ConstContractibleMoorePaths Q) :
    constContractibleMooreEndpoints Q γ =
      (basepointContractibleLoop γ.1.source, basepointContractibleLoop γ.1.target) := by
  simp [constContractibleMooreEndpoints, MoorePath.endpointsBetween_apply]

/-- Evaluation of a two-sphere map at `(north, south) : Sphere2 × Sphere2`. -/
def sphere2Poles : C(C(Sphere2, Q), Q × Q) :=
  (mappingSpaceEval Sphere2.north).prodMk (mappingSpaceEval Sphere2.south)

@[simp]
theorem sphere2Poles_apply (f : C(Sphere2, Q)) :
    sphere2Poles Q f = (f Sphere2.north, f Sphere2.south) := by
  simp [sphere2Poles]

variable {Q}

/-- `ContractibleConstLoopPath Q` is canonically homeomorphic to `unitPathsBetween` from
`range constContractibleLoop` to `range constContractibleLoop` in `𝓛₀Q`. -/
def contractibleConstLoopPathHomeomorphUnitPathsBetween :
    ContractibleConstLoopPath Q ≃ₜ
      unitPathsBetween (Set.range (constContractibleLoop (Q := Q)))
        (Set.range (constContractibleLoop (Q := Q))) where
  toFun p := ⟨p.1, (mem_unitPathsBetween _ _).2
    ⟨let ⟨q, hq⟩ := p.2.1; ⟨q, hq.symm⟩, let ⟨q, hq⟩ := p.2.2; ⟨q, hq.symm⟩⟩⟩
  invFun r :=
    let hr := (mem_unitPathsBetween _ _).1 r.2
    ⟨r.1, ⟨let ⟨q, hq⟩ := hr.1; ⟨q, hq.symm⟩, let ⟨q, hq⟩ := hr.2; ⟨q, hq.symm⟩⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_subtype_val.subtype_mk _
  continuous_invFun := continuous_subtype_val.subtype_mk _

@[simp]
theorem coe_contractibleConstLoopPathHomeomorphUnitPathsBetween (p : ContractibleConstLoopPath Q) :
    (contractibleConstLoopPathHomeomorphUnitPathsBetween p : C(I, contractibleLoops Q)) = p.1 :=
  (rfl)

@[simp]
theorem coe_contractibleConstLoopPathHomeomorphUnitPathsBetween_symm
    (r : unitPathsBetween (Set.range (constContractibleLoop (Q := Q)))
      (Set.range (constContractibleLoop (Q := Q)))) :
    (contractibleConstLoopPathHomeomorphUnitPathsBetween.symm r).1 = r.1 :=
  (rfl)

variable (Q) in
/-- Homeomorphism `C(Sphere2, Q) ≃ₜ unitPathsBetween (range constContractibleLoop)
(range constContractibleLoop)` composing suspension currying with the `unitPathsBetween`
identification. -/
def sphere2HomeomorphUnitPathsBetween :
    C(Sphere2, Q) ≃ₜ
      unitPathsBetween (Set.range (constContractibleLoop (Q := Q)))
        (Set.range (constContractibleLoop (Q := Q))) :=
  sphere2HomeomorphContractibleConstLoopPath.trans
    contractibleConstLoopPathHomeomorphUnitPathsBetween

@[simp]
theorem sphere2HomeomorphUnitPathsBetween_apply (f : C(Sphere2, Q)) (t : I) (z : Circle) :
    ((sphere2HomeomorphUnitPathsBetween Q f).1 t : C(Circle, Q)) z =
      f (suspensionToSphere (t, z)) := by
  simp [sphere2HomeomorphUnitPathsBetween]

@[simp]
theorem sphere2HomeomorphUnitPathsBetween_symm_apply
    (r : unitPathsBetween (Set.range (constContractibleLoop (Q := Q)))
      (Set.range (constContractibleLoop (Q := Q))))
    (t : I) (z : Circle) :
    (sphere2HomeomorphUnitPathsBetween Q).symm r (suspensionToSphere (t, z)) =
      (r.1 t : C(Circle, Q)) z := by
  simp [sphere2HomeomorphUnitPathsBetween]

theorem sphere2Poles_sphere2HomeomorphUnitPathsBetween_symm
    (r : unitPathsBetween (Set.range (constContractibleLoop (Q := Q)))
      (Set.range (constContractibleLoop (Q := Q)))) :
    sphere2Poles Q ((sphere2HomeomorphUnitPathsBetween Q).symm r) =
      constContractibleRangeToProd Q
        (MoorePath.unitEndpointsBetween (Set.range (constContractibleLoop (Q := Q)))
          (Set.range (constContractibleLoop (Q := Q))) r) := by
  have hn : suspensionToSphere (0, 1) = Sphere2.north :=
    (suspensionToSphere_eq_north_iff (0, 1)).2 rfl
  have hs : suspensionToSphere (1, 1) = Sphere2.south :=
    (suspensionToSphere_eq_south_iff (1, 1)).2 rfl
  rw [sphere2Poles_apply, ← hn, ← hs, sphere2HomeomorphUnitPathsBetween_symm_apply,
    sphere2HomeomorphUnitPathsBetween_symm_apply]
  simp [MoorePath.unitEndpointsBetween_apply]

variable (Q) in
/-- **`P_{Q→Q} 𝓛₀Q` is fibre homotopy equivalent to `Map(S², Q)` over `Q × Q`.** -/
def sphere2FiberHomotopyEquivMoorePaths :
    FiberHomotopyEquiv (constContractibleMooreEndpoints Q) (sphere2Poles Q) :=
  ((MoorePath.fiberHomotopyEquivPathsBetween
      (Set.range (constContractibleLoop (Q := Q)))
      (Set.range (constContractibleLoop (Q := Q)))).compBase
    (constContractibleRangeToProd Q)).trans
    (.ofHomeomorph (sphere2HomeomorphUnitPathsBetween Q).symm
      (ContinuousMap.ext sphere2Poles_sphere2HomeomorphUnitPathsBetween_symm))

@[simp]
theorem sphere2FiberHomotopyEquivMoorePaths_toFun :
    (sphere2FiberHomotopyEquivMoorePaths Q).toFun =
      ((sphere2HomeomorphUnitPathsBetween Q).symm : C(_, C(Sphere2, Q))).comp
        (MoorePath.toUnitPathBetween (Set.range (constContractibleLoop (Q := Q)))
          (Set.range (constContractibleLoop (Q := Q)))) := by
  simp [sphere2FiberHomotopyEquivMoorePaths]

@[simp]
theorem sphere2FiberHomotopyEquivMoorePaths_invFun :
    (sphere2FiberHomotopyEquivMoorePaths Q).invFun =
      (MoorePath.ofUnitPathBetween (Set.range (constContractibleLoop (Q := Q)))
          (Set.range (constContractibleLoop (Q := Q)))).comp
        (sphere2HomeomorphUnitPathsBetween Q : C(C(Sphere2, Q), _)) := by
  simp [sphere2FiberHomotopyEquivMoorePaths]

variable (Q) in
/-- **`P_{Q→Q} 𝓛₀Q` is homotopy equivalent to `Map(S², Q)`.** -/
def sphere2HomotopyEquivMoorePaths :
    ConstContractibleMoorePaths Q ≃ₕ C(Sphere2, Q) :=
  (sphere2FiberHomotopyEquivMoorePaths Q).toHomotopyEquiv

@[simp]
theorem sphere2HomotopyEquivMoorePaths_apply_suspensionToSphere
    (γ : ConstContractibleMoorePaths Q) (t : I) (z : Circle) :
    sphere2HomotopyEquivMoorePaths Q γ (suspensionToSphere (t, z)) =
      (γ.1.toUnitPath t : C(Circle, Q)) z := by
  rw [sphere2HomotopyEquivMoorePaths, FiberHomotopyEquiv.toHomotopyEquiv_apply]
  simp

@[simp]
theorem sphere2HomotopyEquivMoorePaths_apply_north (γ : ConstContractibleMoorePaths Q) :
    sphere2HomotopyEquivMoorePaths Q γ Sphere2.north =
      basepointContractibleLoop γ.1.source := by
  rw [sphere2HomotopyEquivMoorePaths, FiberHomotopyEquiv.toHomotopyEquiv_apply]
  have h := congrArg Prod.fst
    (DFunLike.congr_fun (sphere2FiberHomotopyEquivMoorePaths Q).comp_toFun γ)
  simpa using h

@[simp]
theorem sphere2HomotopyEquivMoorePaths_apply_south (γ : ConstContractibleMoorePaths Q) :
    sphere2HomotopyEquivMoorePaths Q γ Sphere2.south =
      basepointContractibleLoop γ.1.target := by
  rw [sphere2HomotopyEquivMoorePaths, FiberHomotopyEquiv.toHomotopyEquiv_apply]
  have h := congrArg Prod.snd
    (DFunLike.congr_fun (sphere2FiberHomotopyEquivMoorePaths Q).comp_toFun γ)
  simpa using h

@[simp]
theorem sphere2HomotopyEquivMoorePaths_symm_apply (f : C(Sphere2, Q)) :
    (sphere2HomotopyEquivMoorePaths Q).symm f =
      MoorePath.ofUnitPathBetween (Set.range (constContractibleLoop (Q := Q)))
        (Set.range (constContractibleLoop (Q := Q)))
        (sphere2HomeomorphUnitPathsBetween Q f) := by
  rw [sphere2HomotopyEquivMoorePaths, FiberHomotopyEquiv.toHomotopyEquiv_symm_apply]
  simp

variable (Q) in
/-- Constant duration-zero Moore paths of constant contractible loops, `Q → P_{Q→Q} 𝓛₀Q`. -/
def constContractibleMooreSection : C(Q, ConstContractibleMoorePaths Q) :=
  (MoorePath.constantBetween (Set.range (constContractibleLoop (Q := Q)))
      (Set.range (constContractibleLoop (Q := Q)))).comp
    ⟨fun q ↦ ⟨constContractibleLoop q, ⟨q, rfl⟩, ⟨q, rfl⟩⟩,
      constContractibleLoop.continuous.subtype_mk _⟩

@[simp]
theorem coe_constContractibleMooreSection (q : Q) :
    (constContractibleMooreSection Q q : MoorePath (contractibleLoops Q)) =
      MoorePath.refl (constContractibleLoop q) := by
  simp [constContractibleMooreSection]

/-- Forward comparison sends `constContractibleMooreSection Q` to constant sphere maps. -/
theorem sphere2FiberHomotopyEquivMoorePaths_toFun_comp_constContractibleMooreSection :
    (sphere2FiberHomotopyEquivMoorePaths Q).toFun.comp (constContractibleMooreSection Q) =
      ContinuousMap.const' := by
  ext q s
  obtain ⟨⟨t, z⟩, rfl⟩ := suspensionToSphere_surjective s
  simp

/-- Reverse image of constant sphere maps shrinks to `constContractibleMooreSection Q` through
sections over the diagonal of `Q × Q`. -/
def sphere2ConstMooreSectionHomotopy :
    ContinuousMap.HomotopyWith
      ((sphere2FiberHomotopyEquivMoorePaths Q).invFun.comp ContinuousMap.const')
      (constContractibleMooreSection Q)
      (fun h ↦ ∀ q, constContractibleMooreEndpoints Q (h q) = (q, q)) where
  toFun p := MoorePath.constantBetweenHomotopy
    (Set.range (constContractibleLoop (Q := Q)))
    (Set.range (constContractibleLoop (Q := Q)))
    (p.1, ⟨constContractibleLoop p.2, ⟨p.2, rfl⟩, ⟨p.2, rfl⟩⟩)
  continuous_toFun := (MoorePath.constantBetweenHomotopy _ _).continuous.comp
    (continuous_fst.prodMk ((constContractibleLoop.continuous.comp continuous_snd).subtype_mk _))
  map_zero_left q := by
    apply Subtype.ext
    have hpath : (sphere2HomeomorphUnitPathsBetween Q (ContinuousMap.const Sphere2 q)).1 =
        ContinuousMap.const I (constContractibleLoop q) := by
      ext t z
      simp
    simp [hpath]
  map_one_left q := Subtype.ext (by simp)
  prop' s q := by simp

end Sphere2

/-! ### Based two-sphere maps and Moore paths from `⋆` to `Q` in `𝓛₀Q` -/

section BasedSphere2

variable (Q : Type*) [TopologicalSpace Q] (x : Q)

/-- Moore paths in `𝓛₀Q` from `constContractibleLoop x` to a constant loop (`P_{⋆→Q} 𝓛₀Q`). -/
abbrev BasedConstContractibleMoorePaths : Type _ :=
  MoorePath.pathsBetween {constContractibleLoop x}
    (Set.range (constContractibleLoop (Q := Q)))

/-- Project `{constContractibleLoop x} × range constContractibleLoop → Q` via the target loop. -/
def basedConstContractibleRangeToTarget :
    C(↥({constContractibleLoop x} : Set (contractibleLoops Q)) ×
      ↥(Set.range (constContractibleLoop (Q := Q))), Q) :=
  (basepointContractibleLoop.comp (ContinuousMap.subtypeVal _)).comp ContinuousMap.snd

/-- Target evaluation `P_{⋆→Q} 𝓛₀Q → Q`. -/
def basedConstContractibleMooreTarget : C(BasedConstContractibleMoorePaths Q x, Q) :=
  (basedConstContractibleRangeToTarget Q x).comp
    (MoorePath.endpointsBetween {constContractibleLoop x}
      (Set.range (constContractibleLoop (Q := Q))))

@[simp]
theorem basedConstContractibleMooreTarget_apply (γ : BasedConstContractibleMoorePaths Q x) :
    basedConstContractibleMooreTarget Q x γ = basepointContractibleLoop γ.1.target := by
  simp [basedConstContractibleMooreTarget, basedConstContractibleRangeToTarget,
    MoorePath.endpointsBetween_apply]

/-- South-pole evaluation `Map_*(S², Q) → Q`. -/
def basedMapSphere2South : C(BasedMap Sphere2 Q Sphere2.north x, Q) :=
  ⟨fun f ↦ f.1 Sphere2.south,
    (continuous_eval_const Sphere2.south).comp continuous_subtype_val⟩

@[simp]
theorem basedMapSphere2South_apply (f : BasedMap Sphere2 Q Sphere2.north x) :
    basedMapSphere2South Q x f = f.1 Sphere2.south :=
  (rfl)

variable {Q x}

/-- `BasedContractibleConstLoopPath Q x` is canonically homeomorphic to `unitPathsBetween` from
`{constContractibleLoop x}` to `range constContractibleLoop` in `𝓛₀Q`. -/
def basedContractibleConstLoopPathHomeomorphUnitPathsBetween (x : Q) :
    BasedContractibleConstLoopPath Q x ≃ₜ
      unitPathsBetween {constContractibleLoop x}
        (Set.range (constContractibleLoop (Q := Q))) where
  toFun p := ⟨p.1.1, (mem_unitPathsBetween _ _).2 ⟨p.2, let ⟨q, hq⟩ := p.1.2.2; ⟨q, hq.symm⟩⟩⟩
  invFun r :=
    let hr := (mem_unitPathsBetween _ _).1 r.2
    ⟨⟨r.1, ⟨⟨x, hr.1⟩, let ⟨q, hq⟩ := hr.2; ⟨q, hq.symm⟩⟩⟩, hr.1⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_subtype_val.subtype_val.subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

@[simp]
theorem coe_basedContractibleConstLoopPathHomeomorphUnitPathsBetween (x : Q)
    (p : BasedContractibleConstLoopPath Q x) :
    (basedContractibleConstLoopPathHomeomorphUnitPathsBetween x p : C(I, contractibleLoops Q)) =
      p.1.1 :=
  (rfl)

@[simp]
theorem coe_basedContractibleConstLoopPathHomeomorphUnitPathsBetween_symm (x : Q)
    (r : unitPathsBetween {constContractibleLoop x}
      (Set.range (constContractibleLoop (Q := Q)))) :
    ((basedContractibleConstLoopPathHomeomorphUnitPathsBetween x).symm r).1.1 = r.1 :=
  (rfl)

variable (Q x) in
/-- Homeomorphism `BasedMap Sphere2 Q Sphere2.north x ≃ₜ unitPathsBetween {constContractibleLoop x}
(range constContractibleLoop)`. -/
def basedMapSphere2HomeomorphUnitPathsBetween :
    BasedMap Sphere2 Q Sphere2.north x ≃ₜ
      unitPathsBetween {constContractibleLoop x}
        (Set.range (constContractibleLoop (Q := Q))) :=
  (basedMapSphere2HomeomorphBasedContractibleConstLoopPath x).trans
    (basedContractibleConstLoopPathHomeomorphUnitPathsBetween x)

@[simp]
theorem basedMapSphere2HomeomorphUnitPathsBetween_apply
    (f : BasedMap Sphere2 Q Sphere2.north x) (t : I) (z : Circle) :
    ((basedMapSphere2HomeomorphUnitPathsBetween Q x f).1 t : C(Circle, Q)) z =
      f.1 (suspensionToSphere (t, z)) := by
  simp [basedMapSphere2HomeomorphUnitPathsBetween]

@[simp]
theorem basedMapSphere2HomeomorphUnitPathsBetween_symm_apply
    (r : unitPathsBetween {constContractibleLoop x}
      (Set.range (constContractibleLoop (Q := Q))))
    (t : I) (z : Circle) :
    ((basedMapSphere2HomeomorphUnitPathsBetween Q x).symm r).1 (suspensionToSphere (t, z)) =
      (r.1 t : C(Circle, Q)) z := by
  simp [basedMapSphere2HomeomorphUnitPathsBetween]

theorem basedMapSphere2South_basedMapSphere2HomeomorphUnitPathsBetween_symm
    (r : unitPathsBetween {constContractibleLoop x}
      (Set.range (constContractibleLoop (Q := Q)))) :
    basedMapSphere2South Q x ((basedMapSphere2HomeomorphUnitPathsBetween Q x).symm r) =
      basedConstContractibleRangeToTarget Q x
        (MoorePath.unitEndpointsBetween {constContractibleLoop x}
          (Set.range (constContractibleLoop (Q := Q))) r) := by
  have hs : suspensionToSphere (1, 1) = Sphere2.south :=
    (suspensionToSphere_eq_south_iff (1, 1)).2 rfl
  rw [basedMapSphere2South_apply, ← hs, basedMapSphere2HomeomorphUnitPathsBetween_symm_apply]
  simp [basedConstContractibleRangeToTarget, MoorePath.unitEndpointsBetween_apply]

variable (Q x) in
/-- **`P_{⋆→Q} 𝓛₀Q` is fibre homotopy equivalent to `Map_*(S², Q)` over south-pole evaluation.** -/
def basedMapSphere2FiberHomotopyEquivMoorePaths :
    FiberHomotopyEquiv (basedConstContractibleMooreTarget Q x) (basedMapSphere2South Q x) :=
  ((MoorePath.fiberHomotopyEquivPathsBetween
      {constContractibleLoop x}
      (Set.range (constContractibleLoop (Q := Q)))).compBase
    (basedConstContractibleRangeToTarget Q x)).trans
    (.ofHomeomorph (basedMapSphere2HomeomorphUnitPathsBetween Q x).symm
      (ContinuousMap.ext basedMapSphere2South_basedMapSphere2HomeomorphUnitPathsBetween_symm))

@[simp]
theorem basedMapSphere2FiberHomotopyEquivMoorePaths_toFun :
    (basedMapSphere2FiberHomotopyEquivMoorePaths Q x).toFun =
      ((basedMapSphere2HomeomorphUnitPathsBetween Q x).symm : C(_, _)).comp
        (MoorePath.toUnitPathBetween {constContractibleLoop x}
          (Set.range (constContractibleLoop (Q := Q)))) := by
  simp [basedMapSphere2FiberHomotopyEquivMoorePaths]

@[simp]
theorem basedMapSphere2FiberHomotopyEquivMoorePaths_invFun :
    (basedMapSphere2FiberHomotopyEquivMoorePaths Q x).invFun =
      (MoorePath.ofUnitPathBetween {constContractibleLoop x}
          (Set.range (constContractibleLoop (Q := Q)))).comp
        (basedMapSphere2HomeomorphUnitPathsBetween Q x : C(_, _)) := by
  simp [basedMapSphere2FiberHomotopyEquivMoorePaths]

variable (Q x) in
/-- **`P_{⋆→Q} 𝓛₀Q` is homotopy equivalent to `Map_*(S², Q)`.** -/
def basedMapSphere2HomotopyEquivMoorePaths :
    BasedConstContractibleMoorePaths Q x ≃ₕ BasedMap Sphere2 Q Sphere2.north x :=
  (basedMapSphere2FiberHomotopyEquivMoorePaths Q x).toHomotopyEquiv

@[simp]
theorem basedMapSphere2HomotopyEquivMoorePaths_apply_suspensionToSphere
    (γ : BasedConstContractibleMoorePaths Q x) (t : I) (z : Circle) :
    (basedMapSphere2HomotopyEquivMoorePaths Q x γ).1 (suspensionToSphere (t, z)) =
      (γ.1.toUnitPath t : C(Circle, Q)) z := by
  rw [basedMapSphere2HomotopyEquivMoorePaths, FiberHomotopyEquiv.toHomotopyEquiv_apply]
  simp

@[simp]
theorem basedMapSphere2HomotopyEquivMoorePaths_apply_south
    (γ : BasedConstContractibleMoorePaths Q x) :
    (basedMapSphere2HomotopyEquivMoorePaths Q x γ).1 Sphere2.south =
      basepointContractibleLoop γ.1.target := by
  rw [basedMapSphere2HomotopyEquivMoorePaths, FiberHomotopyEquiv.toHomotopyEquiv_apply]
  have h := DFunLike.congr_fun (basedMapSphere2FiberHomotopyEquivMoorePaths Q x).comp_toFun γ
  simpa using h

@[simp]
theorem basedMapSphere2HomotopyEquivMoorePaths_symm_apply
    (f : BasedMap Sphere2 Q Sphere2.north x) :
    (basedMapSphere2HomotopyEquivMoorePaths Q x).symm f =
      MoorePath.ofUnitPathBetween {constContractibleLoop x}
        (Set.range (constContractibleLoop (Q := Q)))
        (basedMapSphere2HomeomorphUnitPathsBetween Q x f) := by
  rw [basedMapSphere2HomotopyEquivMoorePaths, FiberHomotopyEquiv.toHomotopyEquiv_symm_apply]
  simp

variable (Q x) in
/-- The duration-zero constant Moore path at `constContractibleLoop x` in `P_{⋆→Q} 𝓛₀Q`. -/
def basedConstContractibleMooreRefl : BasedConstContractibleMoorePaths Q x :=
  MoorePath.constantBetween {constContractibleLoop x}
    (Set.range (constContractibleLoop (Q := Q)))
    ⟨constContractibleLoop x, rfl, ⟨x, rfl⟩⟩

@[simp]
theorem basedMapSphere2HomotopyEquivMoorePaths_refl :
    basedMapSphere2HomotopyEquivMoorePaths Q x (basedConstContractibleMooreRefl Q x) =
      ⟨ContinuousMap.const Sphere2 x, rfl⟩ := by
  apply Subtype.ext
  ext s
  obtain ⟨⟨t, z⟩, rfl⟩ := suspensionToSphere_surjective s
  simp [basedConstContractibleMooreRefl]

end BasedSphere2

end TauCeti
