/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.ImplicitAtlas.DeformationSpace.Basic
import TauCeti.Topology.Constructions.Pi

/-!
# Corner charts of deformation spaces

Let `𝒜` be an implicit atlas of virtual dimension `d` on `X`, and let `I ⊆ J ⊆ B` be finite sets
of indices. The deformation space `D_(I,J,B)` (`TauCeti.ImplicitAtlas.deformationSpace`) is
locally a topological manifold with corners of dimension `d + m_B + |I|`, where
`m_B = ∑_(α ∈ B) dim E_α` (Pardon, Section 4.2): near each of its points it is homeomorphic to an
open subset of the quadrant `ℝ^N × [0, ∞)^I`, and the corner coordinates are the parameters
`t_α`, `α ∈ I`. This file constructs these charts
(`TauCeti.ImplicitAtlas.exists_homeomorph_deformationSpace`).

At a point `(e, t, x)` of `D_(I,J,B)`, let `S = {α | t_α > 0} ⊆ I` be its positive indices. The
point `x` lies over the regular locus of `X_S`, so the product axiom of the atlas gives a local
homeomorphism `c` of `X_J` onto an open subset of `ℝ^n × E_(J \ S)`, with `n = d + m_S`, whose
second coordinate is the extra obstruction `s_(J \ S)`. The chart is

`(e, t, x) ↦ ((c x).1, e|_(B \ S), t|_I) ∈ ℝ^n × E_(B \ S) × ℝ^I`.

Its inverse recovers the remaining coordinates from the equations `s_α(x) = t_α e_α`: the
parameters `t` vanish off `I`, the point is `x = c⁻¹(u, (t_α e_α)_(α ∈ J \ S))`, and for
`α ∈ S`, where `t_α > 0` near the point, the obstruction coordinate is `e_α = t_α⁻¹ s_α(x)`.
The condition defining `D_(I,J,B)` that `ψ_(S'J)(x)` be regular for the positive indices `S'`
of `t` is open near a point regular for `S ⊆ S'`
(`TauCeti.ImplicitAtlas.Core.exists_isOpen_forall_footprintMap_mem_regLocus`), because
`ψ_(S S') ∘ ψ_(S'J) = ψ_(SJ)` and `ψ_(SS')⁻¹(X_S^reg) ⊆ X_(S')^reg`. The dimension of the model is
`n + m_(B \ S) + |I| = d + m_B + |I|`, whatever `S` is.

Consequently `D_(I,J,B)` is locally compact
(`TauCeti.ImplicitAtlas.locallyCompactSpace_deformationSpace`), for all `I`: parameters at indices
of `I` outside `J` must vanish, so `D_(I,J,B) = D_(I ∩ J,J,B)`
(`TauCeti.ImplicitAtlas.deformationSpace_inter_left`). With the Hausdorff property inherited from
`E_B × ℝ^B × X_J`, this makes `D_(I,J,B)` a space on which K-presheaves, indexed by its compact
subsets, such as the relative chains of the pairs `(D_(I,J,B), D_(I,J,B) \ Z_K)`, are considered.

The hypothesis `I ⊆ J` of the chart cannot be dropped: for `J = B = ∅` and `I = {α}` the
deformation space is `D_(∅,∅,∅) = X_∅^reg`, of dimension `d` rather than `d + 1`.

## Main results

* `TauCeti.ImplicitAtlas.exists_homeomorph_deformationSpace`: the corner charts of `D_(I,J,B)`.
* `TauCeti.ImplicitAtlas.deformationSpace_inter_left`: `D_(I ∩ J,J,B) = D_(I,J,B)`.
* `TauCeti.ImplicitAtlas.locallyCompactSpace_deformationSpace`: `D_(I,J,B)` is locally compact.

## References

* J. Pardon, *An algebraic approach to virtual fundamental cycles on moduli spaces of
  pseudo-holomorphic curves*, Geom. Topol. 20 (2016), 779–1034, Definition 4.2.1 and the
  discussion following it (deformation spaces are topological manifolds with corners).
-/

public section

open Set Topology

namespace TauCeti.ImplicitAtlas

variable {A : Type*} [DecidableEq A] {Γ : A → Type*} [∀ α, Group (Γ α)] [∀ α, Finite (Γ α)]
  {E : A → Type*} [∀ α, NormedAddCommGroup (E α)] [∀ α, NormedSpace ℝ (E α)]
  [∀ α, FiniteDimensional ℝ (E α)] {ρ : ∀ α, Representation ℝ (Γ α) (E α)}
  {T : Finset A → Type*} [∀ I, TopologicalSpace (T I)] [∀ I, T2Space (T I)]
  {act : ∀ I : Finset A, ((α : I) → Γ α) →* (T I ≃ₜ T I)}
  {X : Type*} [TopologicalSpace X] {d : ℤ}

/-! ### The chart maps -/

/-- The forward chart map `(e, t, x) ↦ ((c x).1, e|_(B \ S), t|_I)`. -/
private def chartFwd {n : ℕ} {S I J B : Finset A} (hIB : I ⊆ B)
    (c : T J → EuclideanSpace ℝ (Fin n) × ((α : ↥(J \ S)) → E α))
    (p : ((α : B) → E α) × (B → ℝ) × T J) :
    EuclideanSpace ℝ (Fin n) × ((α : ↥(B \ S)) → E α) × (↥I → ℝ) :=
  ((c p.2.2).1, Finset.restrict₂ Finset.sdiff_subset p.1,
    Finset.restrict₂ (π := fun _ ↦ ℝ) hIB p.2.1)

omit [∀ α, NormedAddCommGroup (E α)] [∀ α, NormedSpace ℝ (E α)] [∀ α, FiniteDimensional ℝ (E α)]
  [∀ I, TopologicalSpace (T I)] [∀ I, T2Space (T I)] in
/-- The corner coordinates of the forward chart map are the restricted parameters `t|_I`. -/
private theorem chartFwd_snd_snd {n : ℕ} {S I J B : Finset A} (hIB : I ⊆ B)
    (c : T J → EuclideanSpace ℝ (Fin n) × ((α : ↥(J \ S)) → E α))
    (p : ((α : B) → E α) × (B → ℝ) × T J) :
    (chartFwd hIB c p).2.2 = Finset.restrict₂ (π := fun _ ↦ ℝ) hIB p.2.1 :=
  rfl

omit [∀ α, NormedSpace ℝ (E α)] [∀ α, FiniteDimensional ℝ (E α)] [∀ I, T2Space (T I)] in
private theorem continuousOn_chartFwd {n : ℕ} {S I J B : Finset A} (hIB : I ⊆ B)
    (c : OpenPartialHomeomorph (T J) (EuclideanSpace ℝ (Fin n) × ((α : ↥(J \ S)) → E α))) :
    ContinuousOn (chartFwd hIB c) {p | p.2.2 ∈ c.source} := by
  unfold chartFwd
  exact (c.continuousOn.comp continuous_snd.snd.continuousOn fun _ h ↦ h).fst.prodMk
      (((Finset.continuous_restrict₂ (A := E) Finset.sdiff_subset).comp continuous_fst).prodMk
        ((Finset.continuous_restrict₂ (A := fun _ ↦ ℝ) hIB).comp continuous_snd.fst)).continuousOn

/-- The argument `(u, (t_α e_α)_(α ∈ J \ S))` of `c⁻¹` in the inverse chart map, where `t` is
extended by zero. -/
private def chartArg {n : ℕ} {S I J B : Finset A} (hJB : J ⊆ B)
    (m : EuclideanSpace ℝ (Fin n) × ((α : ↥(B \ S)) → E α) × (↥I → ℝ)) :
    EuclideanSpace ℝ (Fin n) × ((α : ↥(J \ S)) → E α) :=
  (m.1, fun α ↦
    Finset.extendByZero₂ (π := fun _ ↦ ℝ) B m.2.2 ⟨α, hJB (Finset.mem_sdiff.1 α.property).1⟩ •
      m.2.1 ⟨α, Finset.mem_sdiff.2
        ⟨hJB (Finset.mem_sdiff.1 α.property).1, (Finset.mem_sdiff.1 α.property).2⟩⟩)

omit [∀ α, FiniteDimensional ℝ (E α)] in
/-- The first coordinate of the argument of `c⁻¹` is the coordinate `u` of the model. -/
private theorem chartArg_fst {n : ℕ} {S I J B : Finset A} (hJB : J ⊆ B)
    (m : EuclideanSpace ℝ (Fin n) × ((α : ↥(B \ S)) → E α) × (↥I → ℝ)) :
    (chartArg (E := E) hJB m).1 = m.1 :=
  rfl

omit [∀ α, FiniteDimensional ℝ (E α)] in
private theorem continuous_chartArg {n : ℕ} {S I J B : Finset A} (hJB : J ⊆ B) :
    Continuous (chartArg (E := E) (n := n) (S := S) (I := I) hJB) :=
  continuous_fst.prodMk <| continuous_pi fun _ ↦
    (((continuous_apply _).comp (Finset.continuous_extendByZero₂ (π := fun _ ↦ ℝ) B)).comp
      continuous_snd.snd).smul
      ((continuous_apply _).comp continuous_snd.fst)

variable (𝒜 : ImplicitAtlas Γ E ρ T act X d)

/-- The inverse chart map `(u, f, τ) ↦ (e, τ, x)`, with `τ` extended by zero,
`x = c⁻¹(u, (τ_α f_α)_(α ∈ J \ S))`, and `e_α = τ_α⁻¹ s_α(x)` for `α ∈ S`, `e_α = f_α` otherwise. -/
private noncomputable def chartInv {n : ℕ} {S I J B : Finset A} (hSJ : S ⊆ J) (hJB : J ⊆ B)
    (c : OpenPartialHomeomorph (T J) (EuclideanSpace ℝ (Fin n) × ((α : ↥(J \ S)) → E α)))
    (m : EuclideanSpace ℝ (Fin n) × ((α : ↥(B \ S)) → E α) × (↥I → ℝ)) :
    ((α : B) → E α) × (B → ℝ) × T J :=
  (fun α ↦ if h : α.val ∈ S then
      (Finset.extendByZero₂ (π := fun _ ↦ ℝ) B m.2.2 α)⁻¹ •
        𝒜.kuranishi J ⟨α, hSJ h⟩ (c.symm (chartArg hJB m))
    else m.2.1 ⟨α, Finset.mem_sdiff.2 ⟨α.property, h⟩⟩,
    Finset.extendByZero₂ (π := fun _ ↦ ℝ) B m.2.2, c.symm (chartArg hJB m))

variable {𝒜}

section Chart

variable {n : ℕ} {S I J B : Finset A} (hSI : S ⊆ I) (hIJ : I ⊆ J) (hJB : J ⊆ B)
  {c : OpenPartialHomeomorph (T J) (EuclideanSpace ℝ (Fin n) × ((α : ↥(J \ S)) → E α))}
  (hc : ∀ y ∈ c.source, (c y).2 = kuranishiSdiff 𝒜.kuranishi S J y) {W : Set (T J)}
  (hW : ∀ ⦃S' : Finset A⦄ (_ : S ⊆ S') (hS'J : S' ⊆ J)
    (y : kuranishiZeroSet 𝒜.kuranishi S' J), y.val ∈ W →
      𝒜.footprintMap hS'J y ∈ 𝒜.regLocus S')

include hSI hIJ hc hW in
/-- The inverse chart map lands in the deformation space. -/
private theorem chartInv_mem_deformationSpace
    {m : EuclideanSpace ℝ (Fin n) × ((α : ↥(B \ S)) → E α) × (↥I → ℝ)}
    (hm : chartArg hJB m ∈ c.target ∩ c.symm ⁻¹' W) (hpos : ∀ α : I, α.val ∈ S → 0 < m.2.2 α)
    (hnn : ∀ α, 0 ≤ m.2.2 α) :
    chartInv 𝒜 (hSI.trans hIJ) hJB c m ∈ 𝒜.deformationSpace I hJB := by
  have ht : ∀ α, 0 ≤ Finset.extendByZero₂ (π := fun _ ↦ ℝ) B m.2.2 α :=
    Finset.extendByZero₂_nonneg (π := fun _ ↦ ℝ) hnn
  have htI : ∀ α : B, α.val ∉ I → Finset.extendByZero₂ (π := fun _ ↦ ℝ) B m.2.2 α = 0 :=
    fun α h ↦ Finset.extendByZero₂_of_notMem _ α h
  have hsrc : c.symm (chartArg hJB m) ∈ c.source := c.map_target hm.1
  have hs : ∀ α : J, 𝒜.kuranishi J α (c.symm (chartArg hJB m)) =
      Finset.extendByZero₂ (π := fun _ ↦ ℝ) B m.2.2 ⟨α, hJB α.property⟩ •
        (chartInv 𝒜 (hSI.trans hIJ) hJB c m).1 ⟨α, hJB α.property⟩ := by
    intro α
    by_cases h : α.val ∈ S
    · have hτ : Finset.extendByZero₂ (π := fun _ ↦ ℝ) B m.2.2 ⟨α, hJB α.property⟩ ≠ 0 := by
        rw [Finset.extendByZero₂_of_mem (t := B) _ _ (hSI h)]
        exact (hpos _ h).ne'
      simp only [chartInv, dite_eq_left h, smul_smul, mul_inv_cancel₀ hτ, one_smul]
    · -- Off `S`, the Kuranishi map is the second coordinate of `c`.
      have hα : α.val ∈ J \ S := Finset.mem_sdiff.2 ⟨α.property, h⟩
      have h2 : 𝒜.kuranishi J α (c.symm (chartArg hJB m)) = (chartArg hJB m).2 ⟨α, hα⟩ := by
        have h2 := congrFun (hc _ hsrc) ⟨α, hα⟩
        rw [c.right_inv hm.1, kuranishiSdiff_apply] at h2
        exact h2.symm
      rw [h2]
      simp only [chartInv, dite_eq_right h, chartArg]
  refine mem_deformationSpace_of_footprintMap_mem hIJ hJB ht htI hs ?_
  refine hW (fun α hα ↦ mem_positiveIndices.2 ⟨hJB (hSI.trans hIJ hα), ?_⟩) _ _ hm.2
  simp only [chartInv]
  rw [Finset.extendByZero₂_of_mem (t := B) _ _ (hSI hα)]
  exact hpos _ hα

include hc in
/-- On the deformation space, the argument of `c⁻¹` computed from the forward chart is `c x`: the
equations `s_α(x) = t_α e_α` identify `(t_α e_α)_(α ∈ J \ S)` with `s_(J \ S)(x)`. -/
private theorem chartArg_chartFwd {p : ((α : B) → E α) × (B → ℝ) × T J}
    (hp : p ∈ 𝒜.deformationSpace I hJB) (hpc : p.2.2 ∈ c.source) :
    chartArg hJB (chartFwd (hIJ.trans hJB) c p) = c p.2.2 := by
  refine Prod.ext rfl (funext fun α ↦ ?_)
  have hα := Finset.mem_sdiff.1 α.property
  have hp' := mem_deformationSpace.1 hp
  simp only [chartArg, chartFwd, Finset.restrict₂,
    Finset.extendByZero₂_restrict₂ (π := fun _ ↦ ℝ) (hIJ.trans hJB) hp'.2.1]
  rw [hc _ hpc, kuranishiSdiff_apply, hp'.2.2.1 ⟨α, hα.1⟩]

include hc in
/-- The inverse chart map undoes the forward chart map on the chart domain. -/
private theorem chartInv_chartFwd {p : ((α : B) → E α) × (B → ℝ) × T J}
    (hp : p ∈ 𝒜.deformationSpace I hJB) (hpc : p.2.2 ∈ c.source)
    (hpos : ∀ α : B, α.val ∈ S → 0 < p.2.1 α) :
    chartInv 𝒜 (hSI.trans hIJ) hJB c (chartFwd (hIJ.trans hJB) c p) = p := by
  have harg := chartArg_chartFwd hIJ hJB hc hp hpc
  have ht := Finset.extendByZero₂_restrict₂ (π := fun _ ↦ ℝ) (hIJ.trans hJB)
    (mem_deformationSpace.1 hp).2.1
  refine Prod.ext (funext fun α ↦ ?_) (Prod.ext ?_ ?_)
  · by_cases h : α.val ∈ S
    · simp only [chartInv, dite_eq_left h, harg, c.left_inv hpc]
      rw [chartFwd_snd_snd, ht,
        (mem_deformationSpace.1 hp).2.2.1 ⟨α, hSI.trans hIJ h⟩, smul_smul,
        inv_mul_cancel₀ (hpos α h).ne', one_smul]
    · simp only [chartInv, dite_eq_right h, chartFwd, Finset.restrict₂]
  · exact ht
  · simp only [chartInv, harg, c.left_inv hpc]

/-- The forward chart map undoes the inverse chart map. -/
private theorem chartFwd_chartInv
    {m : EuclideanSpace ℝ (Fin n) × ((α : ↥(B \ S)) → E α) × (↥I → ℝ)}
    (hm : chartArg hJB m ∈ c.target) :
    chartFwd (hIJ.trans hJB) c (chartInv 𝒜 (hSI.trans hIJ) hJB c m) = m := by
  refine Prod.ext ?_ (Prod.ext (funext fun α ↦ ?_) (funext fun α ↦ ?_))
  · simp only [chartFwd, chartInv]
    rw [c.right_inv hm, chartArg_fst]
  · simp only [chartFwd, chartInv, Finset.restrict₂,
      dite_eq_right (Finset.mem_sdiff.1 α.property).2]
  · simp only [chartFwd, chartInv, Finset.restrict₂_extendByZero₂]

/-- The inverse chart map is continuous where `t` is positive on `S` and `c⁻¹` is defined. -/
private theorem continuousOn_chartInv :
    ContinuousOn (chartInv 𝒜 (hSI.trans hIJ) hJB c)
      {m | chartArg hJB m ∈ c.target ∧ ∀ α : I, α.val ∈ S → 0 < m.2.2 α} := by
  have hx : ContinuousOn (fun m ↦ c.symm (chartArg hJB m))
      {m | chartArg hJB m ∈ c.target ∧ ∀ α : I, α.val ∈ S → 0 < m.2.2 α} :=
    c.continuousOn_symm.comp (continuous_chartArg hJB).continuousOn fun _ hm ↦ hm.1
  have ht : Continuous fun m : EuclideanSpace ℝ (Fin n) × ((α : ↥(B \ S)) → E α) × (↥I → ℝ) ↦
      Finset.extendByZero₂ (π := fun _ ↦ ℝ) B m.2.2 :=
    (Finset.continuous_extendByZero₂ (π := fun _ ↦ ℝ) B).comp continuous_snd.snd
  refine ContinuousOn.prodMk (continuousOn_pi.2 fun α ↦ ?_) (ht.continuousOn.prodMk hx)
  by_cases h : α.val ∈ S
  · simp only [dite_eq_left h]
    refine (((continuous_apply α).comp ht).continuousOn.inv₀ fun m hm ↦ ?_).smul
      ((𝒜.continuous_kuranishi J _).comp_continuousOn hx)
    simp only [Function.comp_apply, Finset.extendByZero₂_of_mem _ _ (hSI h)]
    exact (hm.2 _ h).ne'
  · simp only [dite_eq_right h]
    exact ((continuous_apply _).comp continuous_snd.fst).continuousOn

end Chart

/-! ### Corner charts -/

variable {I J B : Finset A}

omit [∀ I, T2Space (T I)] in
/-- The model of the corner chart at a point with positive indices `S ⊆ I ⊆ B`, for the product
model `ℝ^n` of `X_S^reg` with `n = d + m_S`, has dimension `d + m_B + |I|`. -/
private theorem finrank_chartModel {S : Finset A} (hSB : S ⊆ B) {n : ℕ}
    (hn : (n : ℤ) = d + ∑ α ∈ S, (Module.finrank ℝ (E α) : ℤ)) :
    (Module.finrank ℝ (EuclideanSpace ℝ (Fin n) × ((α : ↥(B \ S)) → E α) × (↥I → ℝ)) : ℤ) =
      d + ∑ α ∈ B, (Module.finrank ℝ (E α) : ℤ) + I.card := by
  rw [Module.finrank_prod, Module.finrank_prod, finrank_euclideanSpace_fin,
    Module.finrank_pi_fintype, Module.finrank_fintype_fun_eq_card, Fintype.card_coe]
  push_cast
  rw [Finset.sum_coe_sort (B \ S) fun α ↦ (Module.finrank ℝ (E α) : ℤ),
    ← Finset.sum_sdiff hSB, hn]
  ring

/-- **Corner charts of deformation spaces** (Pardon, Section 4.2). For `I ⊆ J ⊆ B`, every point
`p = (e, t, x)` of `D_(I,J,B)` has an open neighbourhood `U` homeomorphic to the intersection of an
open set `O` with the quadrant `{(u, f, τ) | τ ≥ 0}` of `ℝ^n × E_(B \ S) × ℝ^I`, where
`S = {α | t_α > 0}`. The model has dimension `d + m_B + |I|`, and the homeomorphism sends a point
`(e', t', x')` to a point whose corner coordinates `τ` are the parameters `t'|_I`. So `D_(I,J,B)` is
locally a topological manifold with corners of dimension `d + m_B + |I|`, whose corner faces are
the faces `t_α = 0`, `α ∈ I`. -/
theorem exists_homeomorph_deformationSpace (hIJ : I ⊆ J) (hJB : J ⊆ B)
    (p : 𝒜.deformationSpace I hJB) :
    ∃ n : ℕ, (Module.finrank ℝ (EuclideanSpace ℝ (Fin n) ×
        ((α : ↥(B \ positiveIndices p.val.2.1)) → E α) × (↥I → ℝ)) : ℤ) =
        d + ∑ α ∈ B, (Module.finrank ℝ (E α) : ℤ) + I.card ∧
      ∃ (U : Set (𝒜.deformationSpace I hJB)) (O : Set (EuclideanSpace ℝ (Fin n) ×
          ((α : ↥(B \ positiveIndices p.val.2.1)) → E α) × (↥I → ℝ))),
        IsOpen U ∧ p ∈ U ∧ IsOpen O ∧ ∃ φ : U ≃ₜ ↥(O ∩ {m | ∀ α, 0 ≤ m.2.2 α}),
          ∀ q, (φ q).val.2.2 =
            Finset.restrict₂ (π := fun _ ↦ ℝ) (hIJ.trans hJB) q.val.val.2.1 := by
  obtain ⟨-, hptI, -, hSJ, hx, hreg⟩ := mem_deformationSpace.1 p.property
  set S := positiveIndices p.val.2.1
  have hSI : S ⊆ I := positiveIndices_subset hptI
  obtain ⟨n, hn, c, hxc, hc⟩ := 𝒜.exists_openPartialHomeomorph hSJ ⟨_, hx⟩ hreg
  obtain ⟨W, hWo, hxW, hW⟩ := 𝒜.exists_isOpen_forall_footprintMap_mem_regLocus hSJ ⟨_, hx⟩ hreg
  refine ⟨n, finrank_chartModel (hSI.trans (hIJ.trans hJB)) hn,
    {q | q.val.2.2 ∈ c.source ∩ W ∧ ∀ α : B, α.val ∈ S → 0 < q.val.2.1 α},
    {m | chartArg hJB m ∈ c.target ∩ c.symm ⁻¹' W ∧ ∀ α : I, α.val ∈ S → 0 < m.2.2 α},
    ?_, ⟨⟨hxc, hxW⟩, fun α hα ↦ (mem_positiveIndices.1 hα).elim fun _ h ↦ h⟩, ?_, ?_⟩
  · simp only [ofPred_and, ofPred_forall]
    exact ((c.open_source.inter hWo).preimage (continuous_snd.snd.comp continuous_subtypeVal)).inter
      (isOpen_iInter_of_finite fun α ↦ isOpen_iInter_of_finite fun _ ↦ isOpen_lt continuous_const
        ((continuous_apply α).comp (continuous_snd.fst.comp continuous_subtypeVal)))
  · simp only [ofPred_and, ofPred_forall]
    exact ((c.isOpen_inter_preimage_symm hWo).preimage (continuous_chartArg hJB)).inter
      (isOpen_iInter_of_finite fun α ↦ isOpen_iInter_of_finite fun _ ↦ isOpen_lt continuous_const
        ((continuous_apply α).comp continuous_snd.snd))
  refine ⟨
    { toFun q := ⟨chartFwd (hIJ.trans hJB) c q.val.val, ⟨?_, fun α hα ↦ q.property.2 _ hα⟩,
        fun α ↦ (mem_deformationSpace.1 q.val.property).1 _⟩
      invFun m := ⟨⟨chartInv 𝒜 (hSI.trans hIJ) hJB c m.val,
          chartInv_mem_deformationSpace hSI hIJ hJB hc hW m.property.1.1 m.property.1.2
            m.property.2⟩,
        ⟨c.map_target m.property.1.1.1, m.property.1.1.2⟩, fun α hα ↦ ?_⟩
      left_inv q := Subtype.ext <| Subtype.ext <|
        chartInv_chartFwd hSI hIJ hJB hc q.val.property q.property.1.1 q.property.2
      right_inv m := Subtype.ext <| chartFwd_chartInv hSI hIJ hJB m.property.1.1.1
      continuous_toFun := ?_
      continuous_invFun := ?_ }, fun _ ↦ rfl⟩
  · rw [chartArg_chartFwd hIJ hJB hc q.val.property q.property.1.1]
    refine ⟨c.map_source q.property.1.1, ?_⟩
    rw [mem_preimage, c.left_inv q.property.1.1]
    exact q.property.1.2
  · simp only [chartInv, Finset.extendByZero₂_of_mem _ _ (hSI hα)]
    exact m.property.1.2 _ hα
  · exact Continuous.subtype_mk ((continuousOn_chartFwd (hIJ.trans hJB) c).comp_continuous
      (continuous_subtypeVal.comp continuous_subtypeVal) fun q ↦ q.property.1.1) _
  · exact Continuous.subtype_mk (Continuous.subtype_mk
      ((continuousOn_chartInv hSI hIJ hJB).comp_continuous continuous_subtypeVal fun m ↦
        ⟨m.property.1.1.1, m.property.1.2⟩) _) _

/-- Parameters at indices of `I` outside `J` vanish on `D_(I,J,B)`, since the positive indices of
its points lie in `J`: so `D_(I ∩ J,J,B) = D_(I,J,B)`. -/
theorem deformationSpace_inter_left (I : Finset A) (hJB : J ⊆ B) :
    𝒜.deformationSpace (I ∩ J) hJB = 𝒜.deformationSpace I hJB := by
  ext p
  simp only [mem_deformationSpace]
  refine ⟨fun ⟨ht, htI, h⟩ ↦ ⟨ht, fun α hα ↦ htI α fun h ↦ hα (Finset.mem_inter.1 h).1, h⟩,
    fun ⟨ht, htI, hs, hSJ, h⟩ ↦ ⟨ht, fun α hα ↦ ?_, hs, hSJ, h⟩⟩
  by_cases hαI : α.val ∈ I
  · exact le_antisymm (not_lt.1 fun hpos ↦ hα (Finset.mem_inter.2
      ⟨hαI, hSJ (mem_positiveIndices.2 ⟨α.property, hpos⟩)⟩)) (ht α)
  · exact htI α hαI

/-- **Deformation spaces are locally compact**: each point of `D_(I,J,B)` has a neighbourhood
homeomorphic to an open subset of a quadrant in a finite-dimensional space. -/
instance locallyCompactSpace_deformationSpace {I : Finset A} {hJB : J ⊆ B} :
    LocallyCompactSpace (𝒜.deformationSpace I hJB) := by
  rw [← deformationSpace_inter_left]
  suffices WeaklyLocallyCompactSpace (𝒜.deformationSpace (I ∩ J) hJB) from inferInstance
  refine ⟨fun p ↦ ?_⟩
  obtain ⟨n, -, U, O, hU, hpU, hO, φ, -⟩ :=
    𝒜.exists_homeomorph_deformationSpace Finset.inter_subset_right hJB p
  have hQ : IsClosed {m : EuclideanSpace ℝ (Fin n) ×
      ((α : ↥(B \ positiveIndices p.val.2.1)) → E α) × (↥(I ∩ J) → ℝ) | ∀ α, 0 ≤ m.2.2 α} := by
    simp only [ofPred_forall]
    exact isClosed_iInter fun α ↦ isClosed_le continuous_const
      ((continuous_apply α).comp continuous_snd.snd)
  have : LocallyCompactSpace U :=
    φ.locallyCompactSpace_iff.2 (hO.isLocallyClosed.inter hQ.isLocallyClosed).locallyCompactSpace
  obtain ⟨K, hK, hKp⟩ := exists_compact_mem_nhds (⟨p, hpU⟩ : U)
  refine ⟨Subtype.val '' K, hK.image continuous_subtypeVal, ?_⟩
  have hmap := hU.isOpenEmbedding_subtypeVal.map_nhds_eq ⟨p, hpU⟩
  rw [← hmap]
  exact Filter.image_mem_map hKp

end TauCeti.ImplicitAtlas
