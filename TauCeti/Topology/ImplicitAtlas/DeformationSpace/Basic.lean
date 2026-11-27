/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Data.Finset.Pi
public import TauCeti.Topology.ImplicitAtlas.Basic
public import TauCeti.Topology.Sets.Compacts
import TauCeti.Algebra.Group.Pi.Finset
import TauCeti.Topology.Constructions.Pi

/-!
# Deformation spaces of implicit atlases

Let `𝒜` be an implicit atlas (`TauCeti.ImplicitAtlas`) of virtual dimension `d` on `X`, with
thickenings `X_I`, Kuranishi maps `s_α`, regular loci `X_I^reg` and footprint maps `ψ_IJ`. For
finite sets of indices `I ⊆ J ⊆ B`, Pardon's **deformation space** `D_(I,J,B)` consists of the
triples `(e, t, x)` with `e ∈ E_B = ∏_(α ∈ B) E_α`, `t ∈ ℝ^B` and `x ∈ X_J` such that

* `t_α ≥ 0` for every `α`, and `t_α = 0` for `α ∈ B \ I`;
* `s_α(x) = t_α e_α` for every `α ∈ J`;
* `ψ_SJ(x) ∈ X_S^reg`, where `S = {α ∈ B | t_α > 0}`.

The set `S` (`TauCeti.ImplicitAtlas.positiveIndices`) is contained in `I`
(`TauCeti.ImplicitAtlas.positiveIndices_subset`), and the equations force `s_α(x) = 0` for
`α ∈ J \ S`, so that `x` lies in the domain of `ψ_SJ`
(`TauCeti.ImplicitAtlas.mem_kuranishiZeroSet_positiveIndices`). The last condition puts `x` in the
regular locus `X_J^reg` (`TauCeti.ImplicitAtlas.mem_regLocus_of_mem_deformationSpace`). Over the
part where `t` is positive, `D_(I,J,B)` is the zero set of the rescaled section `s_α / t_α - e_α`,
while at `t_α = 0` the obstruction coordinate `e_α` becomes free: this interpolation is what the
virtual cochain complexes of the atlas are built from.

This file defines `D_(I,J,B)` (`TauCeti.ImplicitAtlas.deformationSpace`) as a subspace of
`E_B × ℝ^B × X_J`, together with the structure that the virtual complexes use.

* **The action of `Γ_B`** (`TauCeti.ImplicitAtlas.deformationAction`): `g` acts on `E_B` by the
  representations, trivially on `ℝ^B` and on `X_J` through the restriction `Γ_B → Γ_J`. It is a
  homomorphism into the homeomorphisms of `D_(I,J,B)`, and makes `D_(I,J,B)` a space with a
  continuous action of `Γ_B` (`TauCeti.ImplicitAtlas.instMulActionDeformationSpace`).
* **The supports** (`TauCeti.ImplicitAtlas.deformationSupport`): for `K ⊆ X`, the set
  `Z_K ⊆ D_(I,J,B)` of the points with `e = 0` and `ψ_∅J(x) ∈ K`. It is monotone in `K`
  (`TauCeti.ImplicitAtlas.deformationSupport_mono`), closed when `K` is
  (`TauCeti.ImplicitAtlas.isClosed_deformationSupport`), continuous along the compact
  neighbourhoods of a compact `K` when `X` is locally compact Hausdorff
  (`TauCeti.ImplicitAtlas.exists_mem_compactNhds_disjoint_deformationSupport`), and invariant under
  `Γ_B`
  (`TauCeti.ImplicitAtlas.deformationAction_mem_deformationSupport_iff`). For `I ⊆ J`, the
  supports lie over the intersection `V_I ∩ V_J` of the regular footprints, and every point of
  `V_I ∩ V_J` lies under one of them, so `Z_K` is nonempty exactly when `K` meets `V_I ∩ V_J`
  (`TauCeti.ImplicitAtlas.nonempty_deformationSupport_iff`).
* **The comparison maps** (`TauCeti.ImplicitAtlas.deformationMap`): for `I ⊆ I'`, `I ⊆ J'`,
  `J' ⊆ J ⊆ B ⊆ B'`, the continuous map `D_(I,J,B) × E_(B' \ B) → D_(I',J',B')` that puts the new
  obstruction coordinates in `E_(B' \ B)`, extends `t` by zero and applies `ψ_J'J` to `x`. These
  maps compose (`TauCeti.ImplicitAtlas.deformationMap_deformationMap`), the map from `(I, J, B)`
  to itself is the identity (`TauCeti.ImplicitAtlas.deformationMap_self`), they are equivariant
  (`TauCeti.ImplicitAtlas.deformationMap_deformationAction`) and are maps of pairs: the image of
  `(p, e')` lies in `Z_K` exactly when `p ∈ Z_K` and `e' = 0`
  (`TauCeti.ImplicitAtlas.deformationMap_mem_deformationSupport_iff`). For `B = B'` they are the
  arrows of the interval diagram of the virtual complex, and for `B ⊆ B'` they compare a finite
  subatlas with a larger one.

Pardon's conditions `I ⊆ I' ⊆ J'` are relaxed to `I ⊆ I'` and `I ⊆ J'`, which is all the
construction uses. The physical boundary piece of `D_(I,J,B)`, for atlases with boundary, is not
treated here. The corner charts exhibiting `D_(I,J,B)` as a topological manifold with corners
(`TauCeti.ImplicitAtlas.exists_homeomorph_deformationSpace`) and its local compactness
(`TauCeti.ImplicitAtlas.locallyCompactSpace_deformationSpace`) are in
`TauCeti.Topology.ImplicitAtlas.DeformationSpace.Chart`.

## Checks

* For `I = J = B = ∅`, the deformation space is the regular locus `X_∅^reg`
  (`TauCeti.ImplicitAtlas.mem_deformationSpace_empty_iff`) and `Z_K` is the part over `K`
  (`TauCeti.ImplicitAtlas.mem_deformationSupport_empty_iff`).
* `D_(I,J,B)` is empty when the regular loci `X_S^reg` are empty for all `S ⊆ I`
  (`TauCeti.ImplicitAtlas.deformationSpace_eq_empty`).

The deformation spaces of the atlas `s(x) = xᵐ` on a point are computed in
`TauCeti.Topology.ImplicitAtlas.Examples`.

## References

* J. Pardon, *An algebraic approach to virtual fundamental cycles on moduli spaces of
  pseudo-holomorphic curves*, Geom. Topol. 20 (2016), 779–1034, Definition 4.2.1 (deformation
  spaces) and Definition 4.2.5 (the virtual complexes built from them).
-/

public section

open Set Topology

namespace TauCeti.ImplicitAtlas

variable {A : Type*}

/-- The indices `S = {α ∈ B | t_α > 0}` at which a parameter `t ∈ ℝ^B` is positive, as a finite
set of indices. -/
noncomputable def positiveIndices {B : Finset A} (t : B → ℝ) : Finset A :=
  (Finset.univ.filter fun α : B ↦ 0 < t α).map (Function.Embedding.subtype _)

@[simp]
theorem mem_positiveIndices {B : Finset A} {t : B → ℝ} {α : A} :
    α ∈ positiveIndices t ↔ ∃ h : α ∈ B, 0 < t ⟨α, h⟩ := by
  simp [positiveIndices]

/-- If `t` vanishes off `I`, then `t` is positive only at indices of `I`. -/
theorem positiveIndices_subset {I B : Finset A} {t : B → ℝ} (ht : ∀ α : B, α.val ∉ I → t α = 0) :
    positiveIndices t ⊆ I := fun α hα ↦ by
  obtain ⟨h, hpos⟩ := mem_positiveIndices.1 hα
  by_contra hI
  exact hpos.ne' (ht ⟨α, h⟩ hI)

/-- The equations `s_α(x) = t_α e_α` with `t ≥ 0` force `s_α(x) = 0` wherever `t_α` is not
positive, so `x` lies in the zero set `Z_SJ` for `S = {α | t_α > 0}`, the domain of the footprint
map `ψ_SJ` of an implicit atlas with Kuranishi maps `s`. -/
theorem mem_kuranishiZeroSet_positiveIndices {T : Finset A → Type*} {E : A → Type*}
    [∀ α, AddCommMonoid (E α)] [∀ α, Module ℝ (E α)] {s : ∀ (J : Finset A) (α : J), T J → E α}
    {J B : Finset A} (hJB : J ⊆ B) {e : (α : B) → E α} {t : B → ℝ} {x : T J}
    (ht : ∀ α, 0 ≤ t α) (hs : ∀ α : J, s J α x = t ⟨α, hJB α.property⟩ • e ⟨α, hJB α.property⟩) :
    x ∈ kuranishiZeroSet s (positiveIndices t) J :=
  mem_kuranishiZeroSet.2 fun α hα ↦ by
    have h0 : t ⟨α, hJB α.property⟩ = 0 :=
      le_antisymm (not_lt.1 fun h ↦ hα (mem_positiveIndices.2 ⟨_, h⟩)) (ht _)
    rw [hs, h0, zero_smul]

variable [DecidableEq A] {Γ : A → Type*} [∀ α, Group (Γ α)] [∀ α, Finite (Γ α)]
  {E : A → Type*} [∀ α, NormedAddCommGroup (E α)] [∀ α, NormedSpace ℝ (E α)]
  [∀ α, FiniteDimensional ℝ (E α)] {ρ : ∀ α, Representation ℝ (Γ α) (E α)}
  {T : Finset A → Type*} [∀ I, TopologicalSpace (T I)] [∀ I, T2Space (T I)]
  {act : ∀ I : Finset A, ((α : I) → Γ α) →* (T I ≃ₜ T I)}
  {X : Type*} [TopologicalSpace X] {d : ℤ} (𝒜 : ImplicitAtlas Γ E ρ T act X d)

/-! ### The deformation space -/

/-- **The deformation space** `D_(I,J,B)` of an implicit atlas (Pardon, Definition 4.2.1), for
finite sets of indices `J ⊆ B` and `I`: the triples `(e, t, x) ∈ E_B × ℝ^B × X_J` with `t ≥ 0`,
`t_α = 0` for `α ∉ I`, `s_α(x) = t_α e_α` for `α ∈ J`, and `ψ_SJ(x) ∈ X_S^reg` for the set
`S = {α | t_α > 0}`. It carries the subspace topology of `E_B × ℝ^B × X_J`. -/
def deformationSpace (I : Finset A) {J B : Finset A} (hJB : J ⊆ B) :
    Set (((α : B) → E α) × (B → ℝ) × T J) :=
  {p | (∀ α, 0 ≤ p.2.1 α) ∧ (∀ α : B, α.val ∉ I → p.2.1 α = 0) ∧
    (∀ α : J, 𝒜.kuranishi J α p.2.2 = p.2.1 ⟨α, hJB α.property⟩ • p.1 ⟨α, hJB α.property⟩) ∧
    ∃ (h : positiveIndices p.2.1 ⊆ J)
      (hx : p.2.2 ∈ kuranishiZeroSet 𝒜.kuranishi (positiveIndices p.2.1) J),
      𝒜.footprintMap h ⟨p.2.2, hx⟩ ∈ 𝒜.regLocus (positiveIndices p.2.1)}

variable {𝒜}

/-- Membership in the deformation space `D_(I,J,B)`. -/
theorem mem_deformationSpace {I J B : Finset A} {hJB : J ⊆ B}
    {p : ((α : B) → E α) × (B → ℝ) × T J} :
    p ∈ 𝒜.deformationSpace I hJB ↔ (∀ α, 0 ≤ p.2.1 α) ∧ (∀ α : B, α.val ∉ I → p.2.1 α = 0) ∧
      (∀ α : J, 𝒜.kuranishi J α p.2.2 = p.2.1 ⟨α, hJB α.property⟩ • p.1 ⟨α, hJB α.property⟩) ∧
      ∃ (h : positiveIndices p.2.1 ⊆ J)
        (hx : p.2.2 ∈ kuranishiZeroSet 𝒜.kuranishi (positiveIndices p.2.1) J),
        𝒜.footprintMap h ⟨p.2.2, hx⟩ ∈ 𝒜.regLocus (positiveIndices p.2.1) :=
  Iff.rfl

/-- A point of `D_(I,J,B)` lies in the domain `Z_J'J` of `ψ_J'J` whenever `I ⊆ J'`: its
obstruction parameters vanish off `I`. -/
theorem mem_kuranishiZeroSet_of_mem_deformationSpace {I J J' B : Finset A} {hJB : J ⊆ B}
    (hIJ' : I ⊆ J') {p : ((α : B) → E α) × (B → ℝ) × T J}
    (hp : p ∈ 𝒜.deformationSpace I hJB) : p.2.2 ∈ kuranishiZeroSet 𝒜.kuranishi J' J :=
  mem_kuranishiZeroSet.2 fun α hα ↦ by
    rw [hp.2.2.1 α, hp.2.1 ⟨α, hJB α.property⟩ fun hαI ↦ hα (hIJ' hαI), zero_smul]

/-- A triple `(e, t, x)` lies in `D_(I,J,B)` as soon as `t ≥ 0` vanishes off `I`, the equations
`s_α(x) = t_α e_α` hold, and `ψ_SJ(x) ∈ X_S^reg` for `S = {α | t_α > 0}`: the point `x` is
automatically in the domain of `ψ_SJ` (`mem_kuranishiZeroSet_positiveIndices`), and `S ⊆ J` as
soon as `I ⊆ J`. -/
theorem mem_deformationSpace_of_footprintMap_mem {I J B : Finset A} (hIJ : I ⊆ J) (hJB : J ⊆ B)
    {p : ((α : B) → E α) × (B → ℝ) × T J} (ht : ∀ α, 0 ≤ p.2.1 α)
    (htI : ∀ α : B, α.val ∉ I → p.2.1 α = 0)
    (hs : ∀ α : J, 𝒜.kuranishi J α p.2.2 = p.2.1 ⟨α, hJB α.property⟩ • p.1 ⟨α, hJB α.property⟩)
    (hreg : 𝒜.footprintMap ((positiveIndices_subset htI).trans hIJ)
      ⟨p.2.2, mem_kuranishiZeroSet_positiveIndices hJB ht hs⟩ ∈
        𝒜.regLocus (positiveIndices p.2.1)) :
    p ∈ 𝒜.deformationSpace I hJB :=
  ⟨ht, htI, hs, _, _, hreg⟩

/-- The points of `D_(I,J,B)` lie over the regular locus `X_J^reg`. -/
theorem mem_regLocus_of_mem_deformationSpace {I J B : Finset A} {hJB : J ⊆ B}
    {p : ((α : B) → E α) × (B → ℝ) × T J} (hp : p ∈ 𝒜.deformationSpace I hJB) :
    p.2.2 ∈ 𝒜.regLocus J :=
  let ⟨_, _, _, h, hx, hreg⟩ := hp
  𝒜.mem_regLocus_of_footprintMap_mem h ⟨_, hx⟩ hreg

/-- The deformation space `D_(I,J,B)` is empty if the regular loci `X_S^reg` are empty for all
`S ⊆ I`. -/
theorem deformationSpace_eq_empty {I J B : Finset A} {hJB : J ⊆ B}
    (h : ∀ S ⊆ I, 𝒜.regLocus S = ∅) : 𝒜.deformationSpace I hJB = ∅ :=
  eq_empty_of_forall_notMem fun _ ⟨_, htI, _, _, _, hreg⟩ ↦ by
    rwa [h _ (positiveIndices_subset htI)] at hreg

/-! ### The action of `Γ_B` -/

omit [DecidableEq A] [∀ α, Finite (Γ α)] [∀ α, FiniteDimensional ℝ (E α)]
  [∀ I, T2Space (T I)] in
/-- The action of `g ∈ Γ_B` on `E_B × ℝ^B × X_J`: by the representations on `E_B`, trivially on
`ℝ^B`, and on `X_J` through the restriction `Γ_B → Γ_J`. -/
private def deformationSMul (ρ : ∀ α, Representation ℝ (Γ α) (E α))
    (act : ∀ I : Finset A, ((α : I) → Γ α) →* (T I ≃ₜ T I)) {J B : Finset A} (hJB : J ⊆ B)
    (g : (α : B) → Γ α) (p : ((α : B) → E α) × (B → ℝ) × T J) :
    ((α : B) → E α) × (B → ℝ) × T J :=
  (fun α ↦ ρ α (g α) (p.1 α), p.2.1, act J (Finset.restrict₂ hJB g) p.2.2)

omit [DecidableEq A] [∀ α, Finite (Γ α)] [∀ α, FiniteDimensional ℝ (E α)]
  [∀ I, T2Space (T I)] in
private theorem deformationSMul_one {J B : Finset A} (hJB : J ⊆ B)
    (p : ((α : B) → E α) × (B → ℝ) × T J) : deformationSMul ρ act hJB 1 p = p := by
  have h1 : Finset.restrict₂ hJB (1 : (α : B) → Γ α) = 1 := by
    simpa using (Finset.restrict₂MonoidHom Γ hJB).map_one
  simp [deformationSMul, h1]

omit [DecidableEq A] [∀ α, Finite (Γ α)] [∀ α, FiniteDimensional ℝ (E α)]
  [∀ I, T2Space (T I)] in
private theorem deformationSMul_mul {J B : Finset A} (hJB : J ⊆ B) (g g' : (α : B) → Γ α)
    (p : ((α : B) → E α) × (B → ℝ) × T J) :
    deformationSMul ρ act hJB (g * g') p =
      deformationSMul ρ act hJB g (deformationSMul ρ act hJB g' p) := by
  simp [deformationSMul]

omit [DecidableEq A] [∀ α, Finite (Γ α)] [∀ I, T2Space (T I)] in
private theorem continuous_deformationSMul {J B : Finset A} (hJB : J ⊆ B) (g : (α : B) → Γ α) :
    Continuous (deformationSMul ρ act hJB g) :=
  ((continuous_pi fun α : B ↦ (LinearMap.continuous_of_finiteDimensional (ρ α (g α))).comp
    ((continuous_apply α).comp continuous_fst)).prodMk
      (continuous_snd.fst.prodMk ((act J _).continuous.comp continuous_snd.snd)))

variable (𝒜) in
/-- `D_(I,J,B)` is invariant under `Γ_B`. -/
private theorem deformationSMul_mem_deformationSpace {I J B : Finset A} {hJB : J ⊆ B}
    (g : (α : B) → Γ α) {p : ((α : B) → E α) × (B → ℝ) × T J}
    (hp : p ∈ 𝒜.deformationSpace I hJB) :
    deformationSMul ρ act hJB g p ∈ 𝒜.deformationSpace I hJB := by
  obtain ⟨ht, htI, hs, h, hx, hreg⟩ := hp
  refine ⟨ht, htI, fun α ↦ ?_, h, 𝒜.act_mem_kuranishiZeroSet _ hx, ?_⟩
  · simp only [deformationSMul]
    rw [𝒜.kuranishi_act, hs, map_smul]
    simp only [Finset.restrict₂_def]
  · have := 𝒜.footprintMap_act h (Finset.restrict₂ hJB g) ⟨p.2.2, hx⟩
      (𝒜.act_mem_kuranishiZeroSet _ hx)
    simp only [deformationSMul] at this ⊢
    rw [this]
    exact 𝒜.act_mem_regLocus _ _ _ hreg

variable (𝒜) in
/-- **The action of `Γ_B` on `D_(I,J,B)`** by homeomorphisms: `g` acts by the representations
on `E_B`, trivially on `ℝ^B`, and on `X_J` through `Γ_B → Γ_J`. -/
def deformationAction (I : Finset A) {J B : Finset A} (hJB : J ⊆ B) :
    ((α : B) → Γ α) →* (𝒜.deformationSpace I hJB ≃ₜ 𝒜.deformationSpace I hJB) where
  toFun g :=
    { toFun p :=
        ⟨deformationSMul ρ act hJB g p, 𝒜.deformationSMul_mem_deformationSpace g p.property⟩
      invFun p :=
        ⟨deformationSMul ρ act hJB g⁻¹ p, 𝒜.deformationSMul_mem_deformationSpace g⁻¹ p.property⟩
      left_inv p := Subtype.ext <| by
        dsimp only
        rw [← deformationSMul_mul, inv_mul_cancel, deformationSMul_one]
      right_inv p := Subtype.ext <| by
        dsimp only
        rw [← deformationSMul_mul, mul_inv_cancel, deformationSMul_one]
      continuous_toFun := ((continuous_deformationSMul (ρ := ρ) (act := act) hJB g).comp
        continuous_subtypeVal).subtype_mk _
      continuous_invFun := ((continuous_deformationSMul (ρ := ρ) (act := act) hJB g⁻¹).comp
        continuous_subtypeVal).subtype_mk _ }
  map_one' := by
    ext p : 2
    exact deformationSMul_one hJB p.val
  map_mul' g g' := by
    ext p : 2
    exact deformationSMul_mul hJB g g' p.val

@[simp]
theorem val_deformationAction_apply {I J B : Finset A} {hJB : J ⊆ B} (g : (α : B) → Γ α)
    (p : 𝒜.deformationSpace I hJB) :
    (𝒜.deformationAction I hJB g p).val =
      (fun α : B ↦ ρ α (g α) (p.val.1 α), p.val.2.1, act J (Finset.restrict₂ hJB g) p.val.2.2) :=
  (rfl)

/-- `Γ_B` acts on the deformation space `D_(I,J,B)` by `TauCeti.ImplicitAtlas.deformationAction`. -/
instance instMulActionDeformationSpace (I : Finset A) {J B : Finset A} (hJB : J ⊆ B) :
    MulAction ((α : B) → Γ α) (𝒜.deformationSpace I hJB) :=
  MulAction.compHom _ (𝒜.deformationAction I hJB)

/-- An element of `Γ_B` acts on `D_(I,J,B)` by the homeomorphism
`TauCeti.ImplicitAtlas.deformationAction`. -/
theorem deformationSpace_smul_def {I J B : Finset A} {hJB : J ⊆ B} (g : (α : B) → Γ α)
    (p : 𝒜.deformationSpace I hJB) : g • p = 𝒜.deformationAction I hJB g p :=
  (rfl)

instance (I : Finset A) {J B : Finset A} (hJB : J ⊆ B) :
    ContinuousConstSMul ((α : B) → Γ α) (𝒜.deformationSpace I hJB) :=
  ⟨fun g ↦ by simpa only [deformationSpace_smul_def] using (𝒜.deformationAction I hJB g).continuous⟩

/-! ### Supports -/

variable (𝒜) in
/-- The support `Z_K ⊆ D_(I,J,B)` of a subset `K ⊆ X`: the points `(e, t, x)` with `e = 0` and
`ψ_∅J(x) ∈ K`. For `e = 0` the equations give `s_J(x) = 0`, so `ψ_∅J(x)` is defined. -/
def deformationSupport (I : Finset A) {J B : Finset A} (hJB : J ⊆ B) (K : Set X) :
    Set (𝒜.deformationSpace I hJB) :=
  {p | (p : ((α : B) → E α) × (B → ℝ) × T J).1 = 0 ∧
    ∃ hx : (p : ((α : B) → E α) × (B → ℝ) × T J).2.2 ∈ kuranishiZeroSet 𝒜.kuranishi ∅ J,
      𝒜.baseHomeomorph (𝒜.footprintMap (Finset.empty_subset J) ⟨_, hx⟩) ∈ K}

/-- Membership in the support `Z_K ⊆ D_(I,J,B)`. -/
theorem mem_deformationSupport {I J B : Finset A} {hJB : J ⊆ B} {K : Set X}
    {p : 𝒜.deformationSpace I hJB} :
    p ∈ 𝒜.deformationSupport I hJB K ↔ p.val.1 = 0 ∧
      ∃ hx : p.val.2.2 ∈ kuranishiZeroSet 𝒜.kuranishi ∅ J,
        𝒜.baseHomeomorph (𝒜.footprintMap (Finset.empty_subset J) ⟨_, hx⟩) ∈ K :=
  Iff.rfl

/-- At a point of `D_(I,J,B)` with `e = 0`, all Kuranishi maps vanish. -/
theorem mem_kuranishiZeroSet_empty_of_eq_zero {I J B : Finset A} {hJB : J ⊆ B}
    {p : ((α : B) → E α) × (B → ℝ) × T J} (hp : p ∈ 𝒜.deformationSpace I hJB) (he : p.1 = 0) :
    p.2.2 ∈ kuranishiZeroSet 𝒜.kuranishi ∅ J :=
  mem_kuranishiZeroSet.2 fun α _ ↦ by rw [hp.2.2.1 α, he, Pi.zero_apply, smul_zero]

/-- At a point of `D_(I,J,B)` with `e = 0`, membership in the support `Z_K` only asks for
`ψ_∅J(x) ∈ K`. -/
theorem mem_deformationSupport_iff_of_eq_zero {I J B : Finset A} {hJB : J ⊆ B} {K : Set X}
    {p : 𝒜.deformationSpace I hJB} (he : p.val.1 = 0) :
    p ∈ 𝒜.deformationSupport I hJB K ↔ 𝒜.baseHomeomorph
      (𝒜.footprintMap (Finset.empty_subset J)
        ⟨_, mem_kuranishiZeroSet_empty_of_eq_zero p.property he⟩) ∈
        K :=
  ⟨fun ⟨_, _, hK⟩ ↦ hK, fun hK ↦ ⟨he, _, hK⟩⟩

/-- The support `Z_K` is monotone in `K`. -/
theorem deformationSupport_mono {I J B : Finset A} {hJB : J ⊆ B} {K L : Set X} (h : K ⊆ L) :
    𝒜.deformationSupport I hJB K ⊆ 𝒜.deformationSupport I hJB L :=
  fun _ ⟨he, hx, hK⟩ ↦ ⟨he, hx, h hK⟩

variable (𝒜) in
/-- The base point `ψ_∅J(x) ∈ X` of a point `(0, t, x)` of `D_(I,J,B)`, defined on the closed set
of points with `e = 0`, where all Kuranishi maps vanish. -/
private def supportBase (I : Finset A) {J B : Finset A} (hJB : J ⊆ B) :
    {p : 𝒜.deformationSpace I hJB | (p : ((α : B) → E α) × (B → ℝ) × T J).1 = 0} → X :=
  fun p ↦ 𝒜.baseHomeomorph (𝒜.footprintMap (Finset.empty_subset J)
    ⟨_, mem_kuranishiZeroSet_empty_of_eq_zero p.val.property p.property⟩)

variable (𝒜) in
private theorem continuous_supportBase (I : Finset A) {J B : Finset A} (hJB : J ⊆ B) :
    Continuous (supportBase 𝒜 I hJB) :=
  𝒜.baseHomeomorph.continuous.comp <| (𝒜.continuous_footprintMap _).comp <|
    (continuous_snd.comp (continuous_snd.comp
      (continuous_subtypeVal.comp continuous_subtypeVal))).subtype_mk _

variable (𝒜) in
private theorem isClosed_eq_zero (I : Finset A) {J B : Finset A} (hJB : J ⊆ B) :
    IsClosed {p : 𝒜.deformationSpace I hJB | (p : ((α : B) → E α) × (B → ℝ) × T J).1 = 0} :=
  isClosed_eq (continuous_fst.comp continuous_subtypeVal) continuous_const

variable (𝒜) in
/-- The support `Z_K` is the set of points with `e = 0` whose base point lies in `K`. -/
private theorem deformationSupport_eq_image_preimage_supportBase (I : Finset A) {J B : Finset A}
    (hJB : J ⊆ B) (K : Set X) :
    𝒜.deformationSupport I hJB K = (↑) '' (supportBase 𝒜 I hJB ⁻¹' K) := by
  ext p
  exact ⟨fun h ↦ ⟨⟨p, h.1⟩, (mem_deformationSupport_iff_of_eq_zero h.1).1 h, rfl⟩,
    fun ⟨q, hq, hqp⟩ ↦ hqp ▸ (mem_deformationSupport_iff_of_eq_zero q.property).2 hq⟩

/-- The support `Z_K` of a closed set `K` is closed in `D_(I,J,B)`. It need not be compact. -/
theorem isClosed_deformationSupport {I J B : Finset A} {hJB : J ⊆ B} {K : Set X}
    (hK : IsClosed K) : IsClosed (𝒜.deformationSupport I hJB K) := by
  rw [deformationSupport_eq_image_preimage_supportBase]
  exact (isClosed_eq_zero 𝒜 I hJB).isClosedMap_subtypeVal _
    (hK.preimage (continuous_supportBase 𝒜 I hJB))

/-- **The supports are continuous along compact neighbourhoods.** On a locally compact Hausdorff
space `X`, a compact subset `S` of `D_(I,J,B)` disjoint from the support `Z_K` of a compact set `K`
is disjoint from the support `Z_L` of some compact neighbourhood `L` of `K`: the points of `S` with
`e = 0` lie over a compact subset of `X` disjoint from `K`, which some compact neighbourhood of `K`
misses. -/
theorem exists_mem_compactNhds_disjoint_deformationSupport [T2Space X] [LocallyCompactSpace X]
    {I J B : Finset A} {hJB : J ⊆ B} (K : TopologicalSpace.Compacts X)
    {S : Set (𝒜.deformationSpace I hJB)}
    (hS : IsCompact S) (hSK : Disjoint S (𝒜.deformationSupport I hJB K)) :
    ∃ L ∈ K.compactNhds, Disjoint S (𝒜.deformationSupport I hJB L) := by
  -- the base points of the points of `S` with `e = 0` form a compact set disjoint from `K`
  have hC : IsCompact (supportBase 𝒜 I hJB '' ((↑) ⁻¹' S)) :=
    ((isClosed_eq_zero 𝒜 I hJB).isClosedEmbedding_subtypeVal.isCompact_preimage hS).image
      (continuous_supportBase 𝒜 I hJB)
  have hKC : Disjoint (K : Set X) (supportBase 𝒜 I hJB '' ((↑) ⁻¹' S)) := by
    refine Set.disjoint_left.2 fun y hyK ⟨p, hpS, hpy⟩ ↦ Set.disjoint_left.1 hSK hpS ?_
    rw [deformationSupport_eq_image_preimage_supportBase]
    exact ⟨p, Set.mem_preimage.2 (hpy ▸ hyK), rfl⟩
  obtain ⟨L, hL, hLC⟩ := K.exists_mem_compactNhds_disjoint hC.isClosed hKC
  refine ⟨L, hL, Set.disjoint_left.2 fun p hpS hpL ↦ ?_⟩
  rw [deformationSupport_eq_image_preimage_supportBase] at hpL
  obtain ⟨q, hqL, rfl⟩ := hpL
  exact Set.disjoint_left.1 hLC hqL ⟨q, hpS, rfl⟩

/-- The supports are invariant under `Γ_B`. -/
@[simp]
theorem deformationAction_mem_deformationSupport_iff {I J B : Finset A} {hJB : J ⊆ B}
    {K : Set X} (g : (α : B) → Γ α) (p : 𝒜.deformationSpace I hJB) :
    𝒜.deformationAction I hJB g p ∈ 𝒜.deformationSupport I hJB K ↔
      p ∈ 𝒜.deformationSupport I hJB K := by
  have he : (𝒜.deformationAction I hJB g p).val.1 = 0 ↔ p.val.1 = 0 := by
    rw [val_deformationAction_apply]
    refine ⟨fun h ↦ funext fun α ↦ ?_, fun h ↦ funext fun α ↦ by simp [h]⟩
    have := congrArg (ρ α (g α)⁻¹) (congrFun h α)
    rwa [Representation.inv_self_apply, Pi.zero_apply, map_zero] at this
  by_cases h0 : p.val.1 = 0
  · rw [mem_deformationSupport_iff_of_eq_zero (he.2 h0), mem_deformationSupport_iff_of_eq_zero h0]
    refine Eq.to_iff (congrArg (𝒜.baseHomeomorph · ∈ K) ?_)
    refine (𝒜.footprintMap_act (Finset.empty_subset J) (Finset.restrict₂ hJB g)
      ⟨_, mem_kuranishiZeroSet_empty_of_eq_zero p.property h0⟩ _).trans ?_
    rw [Subsingleton.elim (Finset.restrict₂ (Finset.empty_subset J) _) 1, map_one,
      Homeomorph.one_apply]
  · exact iff_of_false (fun h ↦ h0 (he.1 (mem_deformationSupport.1 h).1))
      fun h ↦ h0 (mem_deformationSupport.1 h).1

/-! ### The supports lie over `V_I ∩ V_J` -/

/-- For `I ⊆ J`, a point `(e, t, x)` of `D_(I,J,B)` with `x` in the zero set `Z_∅J` lies over the
intersection `V_I ∩ V_J` of the regular footprints. The point `x` is regular, and so is `ψ_IJ(x)`,
because `ψ_SI(ψ_IJ(x)) = ψ_SJ(x)` is regular for `S = {α | t_α > 0} ⊆ I`. -/
theorem baseHomeomorph_footprintMap_mem_footprint_inter {I J B : Finset A} (hIJ : I ⊆ J)
    {hJB : J ⊆ B} {p : ((α : B) → E α) × (B → ℝ) × T J} (hp : p ∈ 𝒜.deformationSpace I hJB)
    (hx : p.2.2 ∈ kuranishiZeroSet 𝒜.kuranishi ∅ J) :
    𝒜.baseHomeomorph (𝒜.footprintMap (Finset.empty_subset J) ⟨_, hx⟩) ∈
      𝒜.footprint I ∩ 𝒜.footprint J := by
  refine ⟨?_, (𝒜.baseHomeomorph_footprintMap_mem_footprint_iff _).2
    (mem_regLocus_of_mem_deformationSpace hp)⟩
  obtain ⟨-, htI, -, _, hxS, hreg⟩ := hp
  have hSI : positiveIndices p.2.1 ⊆ I := positiveIndices_subset htI
  have hxI : p.2.2 ∈ kuranishiZeroSet 𝒜.kuranishi I J :=
    kuranishiZeroSet_mono _ (Finset.empty_subset I) J hx
  have hreg' : 𝒜.footprintMap hIJ ⟨_, hxI⟩ ∈ 𝒜.regLocus I := by
    refine 𝒜.mem_regLocus_of_footprintMap_mem hSI
      ⟨_, (𝒜.mem_kuranishiZeroSet_iff_footprintMap_mem hIJ ⟨_, hxI⟩).1 hxS⟩ ?_
    rw [𝒜.footprintMap_footprintMap_mk hSI hIJ _ hxS]
    exact hreg
  exact (𝒜.baseHomeomorph_footprintMap_mem_footprint_iff_of_subset hIJ ⟨_, hx⟩).2 hreg'

/-- For `I ⊆ J ⊆ B`, every point `y` of `V_I ∩ V_J` lies under a point of the support
`Z_{y} ⊆ D_(I,J,B)`: the point `(0, t, x)`, with `t` the indicator function of `I` and `x` a
regular zero of `X_J` over `y`. -/
theorem exists_mem_deformationSupport_singleton {I J B : Finset A} (hIJ : I ⊆ J) (hJB : J ⊆ B)
    {y : X} (hy : y ∈ 𝒜.footprint I ∩ 𝒜.footprint J) :
    ∃ p, p ∈ 𝒜.deformationSupport I hJB {y} := by
  obtain ⟨x, -, rfl⟩ := 𝒜.mem_footprint.1 hy.2
  let t : B → ℝ := fun α ↦ if α.val ∈ I then 1 else 0
  have ht : ∀ α, 0 ≤ t α := fun α ↦ by simp only [t]; split_ifs <;> norm_num
  have htI : ∀ α : B, α.val ∉ I → t α = 0 := fun α hα ↦ by simp [t, hα]
  have hs : ∀ α : J, 𝒜.kuranishi J α x.val = t ⟨α, hJB α.property⟩ • (0 : (α : B) → E α)
      ⟨α, hJB α.property⟩ := fun α ↦ by
    rw [Pi.zero_apply, smul_zero]
    exact mem_kuranishiZeroSet.1 x.property α (Finset.notMem_empty _)
  have hpos : positiveIndices t = I := by
    ext α
    simp only [mem_positiveIndices, t]
    refine ⟨fun ⟨_, h⟩ ↦ by_contra fun hα ↦ by simp [hα] at h, fun hα ↦ ⟨hJB (hIJ hα), ?_⟩⟩
    simp [hα]
  -- `ψ_IJ(x)` lies over `y ∈ V_I`, so it is regular.
  have hreg := (𝒜.baseHomeomorph_footprintMap_mem_footprint_iff_of_subset hIJ x).1 hy.1
  -- The regularity condition of `D_(I,J,B)` at `S = {α | t_α > 0} = I`. It is transported along
  -- `hpos` by generalizing `S`: `subst hpos` and `hpos ▸ hreg` fail, since `t` depends on `I`.
  have hregS : ∀ (S : Finset A) (_ : S = I) (h : S ⊆ J)
      (hx : x.val ∈ kuranishiZeroSet 𝒜.kuranishi S J), 𝒜.footprintMap h ⟨_, hx⟩ ∈ 𝒜.regLocus S := by
    rintro S rfl _ _
    exact hreg
  have hp : ((0 : (α : B) → E α), t, x.val) ∈ 𝒜.deformationSpace I hJB :=
    mem_deformationSpace_of_footprintMap_mem hIJ hJB ht htI hs (hregS _ hpos _ _)
  exact ⟨⟨_, hp⟩, (mem_deformationSupport_iff_of_eq_zero (p := ⟨_, hp⟩) rfl).2 rfl⟩

/-- For `I ⊆ J ⊆ B`, the support `Z_K ⊆ D_(I,J,B)` of `K ⊆ X` is nonempty exactly when `K` meets
`V_I ∩ V_J`. -/
theorem nonempty_deformationSupport_iff {I J B : Finset A} (hIJ : I ⊆ J) (hJB : J ⊆ B)
    {K : Set X} :
    (𝒜.deformationSupport I hJB K).Nonempty ↔ (K ∩ (𝒜.footprint I ∩ 𝒜.footprint J)).Nonempty := by
  refine ⟨fun ⟨p, _, hx, hK⟩ ↦ ⟨_, hK, baseHomeomorph_footprintMap_mem_footprint_inter hIJ
    p.property hx⟩, fun ⟨y, hyK, hy⟩ ↦ ?_⟩
  obtain ⟨p, hp⟩ := exists_mem_deformationSupport_singleton hIJ hJB hy
  exact ⟨p, deformationSupport_mono (singleton_subset_iff.2 hyK) hp⟩

/-! ### Comparison maps -/

/-- The point `(e ⊕ e', t ⊕ 0, ψ_J'J(x))` built from `(e, t, x) ∈ D_(I,J,B)` and
`e' ∈ E_(B' \ B)` lies in `D_(I',J',B')`. -/
private theorem extend_mem_deformationSpace {I I' J J' B B' : Finset A} (hII' : I ⊆ I')
    (hIJ' : I ⊆ J') (hJ'J : J' ⊆ J) (hJB : J ⊆ B) (hBB' : B ⊆ B')
    (p : 𝒜.deformationSpace I hJB) (e' : (α : ↥(B' \ B)) → E α) :
    ((fun α : B' ↦
        if h : α.val ∈ B then p.val.1 ⟨α, h⟩ else e' ⟨α, Finset.mem_sdiff.2 ⟨α.property, h⟩⟩),
      Finset.extendByZero₂ (π := fun _ ↦ ℝ) B' p.val.2.1,
      𝒜.footprintMap hJ'J ⟨_, mem_kuranishiZeroSet_of_mem_deformationSpace hIJ' p.property⟩) ∈
      𝒜.deformationSpace I' (hJ'J.trans (hJB.trans hBB')) := by
  obtain ⟨ht, htI, hs, h, hx, hreg⟩ := p.property
  -- The extended parameter `t ⊕ 0` is positive at the same indices as `t`.
  have hpos : positiveIndices (Finset.extendByZero₂ (π := fun _ ↦ ℝ) B' p.val.2.1) =
      positiveIndices p.val.2.1 := by
    ext α
    simp only [mem_positiveIndices, Finset.extendByZero₂_pos_iff (π := fun _ ↦ ℝ)]
    exact ⟨fun ⟨_, hαB, hα⟩ ↦ ⟨hαB, hα⟩, fun ⟨hαB, hα⟩ ↦ ⟨hBB' hαB, hαB, hα⟩⟩
  refine ⟨Finset.extendByZero₂_nonneg (π := fun _ ↦ ℝ) ht,
    fun α hα ↦ Finset.extendByZero₂_eq_zero_of_forall (π := fun _ ↦ ℝ) htI
      fun hαI ↦ hα (hII' hαI), fun α ↦ ?_, ?_⟩
  · simp only [𝒜.kuranishi_footprintMap, hJB (hJ'J α.property), ↓reduceDIte,
      Finset.extendByZero₂_of_mem]
    exact hs ⟨α, hJ'J α.property⟩
  · dsimp only
    rw [hpos]
    have hSJ' : positiveIndices p.val.2.1 ⊆ J' := (positiveIndices_subset htI).trans hIJ'
    have hx' := (𝒜.mem_kuranishiZeroSet_iff_footprintMap_mem (I := positiveIndices p.val.2.1) hJ'J
      ⟨_, mem_kuranishiZeroSet_of_mem_deformationSpace hIJ' p.property⟩).1 hx
    refine ⟨hSJ', hx', ?_⟩
    rwa [𝒜.footprintMap_footprintMap hSJ' hJ'J _ hx' hx]

variable (𝒜) in
/-- **The comparison map** `D_(I,J,B) × E_(B' \ B) → D_(I',J',B')` (Pardon, Section 4.2), for
`I ⊆ I'`, `I ⊆ J'` and `J' ⊆ J ⊆ B ⊆ B'`: a point `(e, t, x)` and new obstruction coordinates
`e' ∈ E_(B' \ B)` go to `(e ⊕ e', t ⊕ 0, ψ_J'J(x))`. -/
def deformationMap {I I' J J' B B' : Finset A} (hII' : I ⊆ I') (hIJ' : I ⊆ J') (hJ'J : J' ⊆ J)
    (hJB : J ⊆ B) (hBB' : B ⊆ B') (p : 𝒜.deformationSpace I hJB)
    (e' : (α : ↥(B' \ B)) → E α) : 𝒜.deformationSpace I' (hJ'J.trans (hJB.trans hBB')) :=
  ⟨_, extend_mem_deformationSpace hII' hIJ' hJ'J hJB hBB' p e'⟩

section DeformationMap

variable {I I' J J' B B' : Finset A} {hII' : I ⊆ I'} {hIJ' : I ⊆ J'} {hJ'J : J' ⊆ J}
  {hJB : J ⊆ B} {hBB' : B ⊆ B'}

/-- The obstruction coordinates of `deformationMap` are the old ones on `B`. -/
@[simp]
theorem val_deformationMap_fst_of_mem (p : 𝒜.deformationSpace I hJB) (e' : (α : ↥(B' \ B)) → E α)
    (α : B') (hα : α.val ∈ B) :
    (𝒜.deformationMap hII' hIJ' hJ'J hJB hBB' p e').val.1 α = p.val.1 ⟨α, hα⟩ := by
  simp [deformationMap, hα]

/-- The obstruction coordinates of `deformationMap` are the new ones on `B' \ B`. -/
@[simp]
theorem val_deformationMap_fst_of_notMem (p : 𝒜.deformationSpace I hJB)
    (e' : (α : ↥(B' \ B)) → E α) (α : B') (hα : α.val ∉ B) :
    (𝒜.deformationMap hII' hIJ' hJ'J hJB hBB' p e').val.1 α =
      e' ⟨α, Finset.mem_sdiff.2 ⟨α.property, hα⟩⟩ := by
  simp [deformationMap, hα]

/-- The parameters of `deformationMap` are the old ones on `B`. -/
@[simp]
theorem val_deformationMap_snd_fst_of_mem (p : 𝒜.deformationSpace I hJB)
    (e' : (α : ↥(B' \ B)) → E α) (α : B') (hα : α.val ∈ B) :
    (𝒜.deformationMap hII' hIJ' hJ'J hJB hBB' p e').val.2.1 α = p.val.2.1 ⟨α, hα⟩ := by
  simp [deformationMap, hα]

/-- The parameters of `deformationMap` vanish on `B' \ B`. -/
@[simp]
theorem val_deformationMap_snd_fst_of_notMem (p : 𝒜.deformationSpace I hJB)
    (e' : (α : ↥(B' \ B)) → E α) (α : B') (hα : α.val ∉ B) :
    (𝒜.deformationMap hII' hIJ' hJ'J hJB hBB' p e').val.2.1 α = 0 := by
  simp [deformationMap, hα]

/-- The thickening coordinate of `deformationMap` is `ψ_J'J(x)`. -/
@[simp]
theorem val_deformationMap_snd_snd (p : 𝒜.deformationSpace I hJB) (e' : (α : ↥(B' \ B)) → E α) :
    (𝒜.deformationMap hII' hIJ' hJ'J hJB hBB' p e').val.2.2 =
      𝒜.footprintMap hJ'J ⟨_, mem_kuranishiZeroSet_of_mem_deformationSpace hIJ' p.property⟩ := by
  simp [deformationMap]

/-- The comparison maps are continuous. -/
theorem continuous_deformationMap :
    Continuous fun q : 𝒜.deformationSpace I hJB × ((α : ↥(B' \ B)) → E α) ↦
      𝒜.deformationMap hII' hIJ' hJ'J hJB hBB' q.1 q.2 := by
  have hval : (fun q : 𝒜.deformationSpace I hJB × ((α : ↥(B' \ B)) → E α) ↦
      (𝒜.deformationMap hII' hIJ' hJ'J hJB hBB' q.1 q.2).val) = fun q ↦
      ((fun α : B' ↦ if h : α.val ∈ B then q.1.val.1 ⟨α, h⟩
          else q.2 ⟨α, Finset.mem_sdiff.2 ⟨α.property, h⟩⟩),
        Finset.extendByZero₂ (π := fun _ ↦ ℝ) B' q.1.val.2.1,
        𝒜.footprintMap hJ'J
          ⟨_, mem_kuranishiZeroSet_of_mem_deformationSpace hIJ' q.1.property⟩) := by
    funext q
    simp [deformationMap]
  refine Topology.IsInducing.subtypeVal.continuous_iff.2 ?_
  rw [Function.comp_def, hval]
  refine Continuous.prodMk ?_ (Continuous.prodMk ?_ ?_)
  · refine continuous_pi fun α ↦ ?_
    by_cases hα : α.val ∈ B
    · simp only [hα, ↓reduceDIte]
      exact (continuous_apply _).comp (continuous_fst.comp (continuous_subtypeVal.comp
        continuous_fst))
    · simp only [hα, ↓reduceDIte]
      exact (continuous_apply _).comp continuous_snd
  · exact (Finset.continuous_extendByZero₂ (π := fun _ ↦ ℝ) B').comp
      (continuous_snd.fst.comp (continuous_subtypeVal.comp continuous_fst))
  · exact (𝒜.continuous_footprintMap hJ'J).comp
      ((continuous_snd.snd.comp (continuous_subtypeVal.comp continuous_fst)).subtype_mk _)

/-- The comparison maps compose: going from `(I, J, B)` to `(I', J', B')` and then to
`(I'', J'', B'')` is the comparison map from `(I, J, B)` to `(I'', J'', B'')`, with the new
obstruction coordinates on `B'' \ B` that restrict to the two given ones on `B' \ B` and on
`B'' \ B'`. -/
theorem deformationMap_deformationMap {I'' J'' B'' : Finset A} (hI'I'' : I' ⊆ I'')
    (hI'J'' : I' ⊆ J'') (hJ''J' : J'' ⊆ J') (hB'B'' : B' ⊆ B'') (p : 𝒜.deformationSpace I hJB)
    (e₁ : (α : ↥(B' \ B)) → E α) (e₂ : (α : ↥(B'' \ B')) → E α)
    (e : (α : ↥(B'' \ B)) → E α)
    (h₁ : Finset.restrict₂ (Finset.sdiff_subset_sdiff hB'B'' subset_rfl) e = e₁)
    (h₂ : Finset.restrict₂ (Finset.sdiff_subset_sdiff subset_rfl hBB') e = e₂) :
    𝒜.deformationMap hI'I'' hI'J'' hJ''J' (hJ'J.trans (hJB.trans hBB')) hB'B''
        (𝒜.deformationMap hII' hIJ' hJ'J hJB hBB' p e₁) e₂ =
      𝒜.deformationMap (hII'.trans hI'I'') (hII'.trans hI'J'') (hJ''J'.trans hJ'J) hJB
        (hBB'.trans hB'B'') p e := by
  subst h₁ h₂
  refine Subtype.ext (Prod.ext (funext fun α ↦ ?_) (Prod.ext (funext fun α ↦ ?_) ?_))
  · by_cases hαB : α.val ∈ B
    · simp [hαB, hBB' hαB]
    · by_cases hαB' : α.val ∈ B' <;> simp [hαB, hαB', Finset.restrict₂_def]
  · by_cases hαB : α.val ∈ B
    · simp [hαB, hBB' hαB]
    · by_cases hαB' : α.val ∈ B' <;> simp [hαB, hαB']
  · simp only [val_deformationMap_snd_snd]
    exact 𝒜.footprintMap_footprintMap hJ''J' hJ'J _ _ _

/-- The comparison map from `(I, J, B)` to itself is the identity. -/
theorem deformationMap_self (hIJ : I ⊆ J) (p : 𝒜.deformationSpace I hJB)
    (e' : (α : ↥(B \ B)) → E α) :
    𝒜.deformationMap subset_rfl hIJ subset_rfl hJB subset_rfl p e' = p := by
  refine Subtype.ext (Prod.ext (funext fun α ↦ ?_) (Prod.ext (funext fun α ↦ ?_) ?_))
  · simp
  · simp
  · rw [val_deformationMap_snd_snd]
    exact 𝒜.footprintMap_self J _

/-- The comparison maps are equivariant for `Γ_B'`, which acts on `D_(I,J,B)` through `Γ_B` and
on `E_(B' \ B)` by the representations. -/
theorem deformationMap_deformationAction (g : (α : B') → Γ α) (p : 𝒜.deformationSpace I hJB)
    (e' : (α : ↥(B' \ B)) → E α) :
    𝒜.deformationMap hII' hIJ' hJ'J hJB hBB' (𝒜.deformationAction I hJB (Finset.restrict₂ hBB' g) p)
        (fun α ↦ ρ α (Finset.restrict₂ Finset.sdiff_subset g α) (e' α)) =
      𝒜.deformationAction I' (hJ'J.trans (hJB.trans hBB')) g
        (𝒜.deformationMap hII' hIJ' hJ'J hJB hBB' p e') := by
  refine Subtype.ext (Prod.ext (funext fun α ↦ ?_) (Prod.ext (funext fun α ↦ ?_) ?_))
  · by_cases hαB : α.val ∈ B
    · simp only [val_deformationAction_apply, val_deformationMap_fst_of_mem _ _ α hαB]
      simp only [Finset.restrict₂_def]
    · simp only [val_deformationAction_apply, val_deformationMap_fst_of_notMem _ _ α hαB]
      simp only [Finset.restrict₂_def]
  · by_cases hαB : α.val ∈ B
    · simp only [val_deformationAction_apply, val_deformationMap_snd_fst_of_mem _ _ α hαB]
    · simp only [val_deformationAction_apply, val_deformationMap_snd_fst_of_notMem _ _ α hαB]
  · simp only [val_deformationAction_apply, val_deformationMap_snd_snd]
    exact 𝒜.footprintMap_act hJ'J (Finset.restrict₂ hJB (Finset.restrict₂ hBB' g))
      ⟨p.val.2.2, mem_kuranishiZeroSet_of_mem_deformationSpace hIJ' p.property⟩ _

/-- The comparison maps are maps of pairs: the image of `(p, e')` lies in the support `Z_K`
exactly when `p ∈ Z_K` and `e' = 0`. -/
@[simp]
theorem deformationMap_mem_deformationSupport_iff {K : Set X} (p : 𝒜.deformationSpace I hJB)
    (e' : (α : ↥(B' \ B)) → E α) :
    𝒜.deformationMap hII' hIJ' hJ'J hJB hBB' p e' ∈
        𝒜.deformationSupport I' (hJ'J.trans (hJB.trans hBB')) K ↔
      p ∈ 𝒜.deformationSupport I hJB K ∧ e' = 0 := by
  have he : (𝒜.deformationMap hII' hIJ' hJ'J hJB hBB' p e').val.1 = 0 ↔ p.val.1 = 0 ∧ e' = 0 := by
    refine ⟨fun h ↦ ⟨funext fun α ↦ ?_, funext fun α ↦ ?_⟩, fun ⟨h₁, h₂⟩ ↦ funext fun α ↦ ?_⟩
    · simpa using congrFun h ⟨α.val, hBB' α.property⟩
    · simpa [(Finset.mem_sdiff.1 α.property).2] using
        congrFun h ⟨α.val, (Finset.mem_sdiff.1 α.property).1⟩
    · by_cases hα : α.val ∈ B <;> simp [hα, h₁, h₂]
  by_cases h0 : p.val.1 = 0 ∧ e' = 0
  · rw [and_iff_left h0.2, mem_deformationSupport_iff_of_eq_zero (he.2 h0),
      mem_deformationSupport_iff_of_eq_zero h0.1]
    exact Eq.to_iff (congrArg (𝒜.baseHomeomorph · ∈ K)
      (𝒜.footprintMap_footprintMap (Finset.empty_subset J') hJ'J _ _ _))
  · exact iff_of_false (fun h ↦ h0 (he.1 (mem_deformationSupport.1 h).1))
      fun h ↦ h0 ⟨(mem_deformationSupport.1 h.1).1, h.2⟩

end DeformationMap

/-! ### Checks -/

/-- For `I = J = B = ∅`, the deformation space `D_(∅,∅,∅)` is the regular locus `X_∅^reg`. -/
theorem mem_deformationSpace_empty_iff
    {p : ((α : (∅ : Finset A)) → E α) × (↥(∅ : Finset A) → ℝ) × T ∅} :
    p ∈ 𝒜.deformationSpace ∅ (subset_refl ∅) ↔ p.2.2 ∈ 𝒜.regLocus ∅ := by
  have hpos : positiveIndices p.2.1 = ∅ := Finset.eq_empty_of_forall_notMem fun α hα ↦ by
    obtain ⟨h, -⟩ := mem_positiveIndices.1 hα
    exact Finset.notMem_empty α h
  rw [mem_deformationSpace, hpos]
  refine ⟨fun ⟨_, _, _, _, _, hreg⟩ ↦ ?_, fun hp ↦ ⟨fun α ↦ (Finset.notMem_empty _ α.property).elim,
    fun α ↦ (Finset.notMem_empty _ α.property).elim,
    fun α ↦ (Finset.notMem_empty _ α.property).elim,
    subset_refl _, mem_kuranishiZeroSet_self _ _, by rwa [𝒜.footprintMap_self]⟩⟩
  rwa [𝒜.footprintMap_self] at hreg

/-- For `I = J = B = ∅`, the support `Z_K ⊆ D_(∅,∅,∅)` is the part of `X_∅^reg` over `K`. -/
theorem mem_deformationSupport_empty_iff {K : Set X}
    {p : 𝒜.deformationSpace ∅ (subset_refl (∅ : Finset A))} :
    p ∈ 𝒜.deformationSupport ∅ (subset_refl ∅) K ↔
      𝒜.baseHomeomorph p.val.2.2 ∈ K := by
  refine ⟨fun ⟨_, _, hK⟩ ↦ ?_, fun hK ↦ ⟨Subsingleton.elim _ _,
    mem_kuranishiZeroSet_self _ _, by rwa [𝒜.footprintMap_self]⟩⟩
  rwa [𝒜.footprintMap_self] at hK

end TauCeti.ImplicitAtlas
