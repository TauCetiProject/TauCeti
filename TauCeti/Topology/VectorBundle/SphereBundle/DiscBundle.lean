/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.FiberBundle.Proper
public import TauCeti.Topology.FiberBundle.Separation
public import TauCeti.Topology.VectorBundle.OrthonormalTrivialization
public import TauCeti.Topology.VectorBundle.SphereBundle.Basic
public import TauCeti.Topology.CWComplex.Classical.FiberBundle
import TauCeti.Topology.VectorBundle.Smul

/-!
# Topology, local triviality, and radial metric-change homeomorphisms of disc bundles

For a real vector bundle `E → B` with normed fibres, `TauCeti.discBundle F E` and
`TauCeti.sphereBundle F E` are the unit disc and unit sphere subsets of `TotalSpace F E`. This file
develops the topological and metric-comparison properties of `discBundle` and `sphereBundle` needed
to put cellular structures on `(D(E), S(E))`:

* `TauCeti.discBundleProj`: the continuous bundle projection `D(E) → B`;
* `TauCeti.isClosed_discBundle` and `TauCeti.isClosed_sphereBundle`: closedness in `TotalSpace F E`
  when the fibre norm is continuous;
* `TauCeti.eq_univ_discBundle_of_subsingleton`, `TauCeti.eq_empty_sphereBundle_of_subsingleton`, and
  `TauCeti.discBundleHomeomorphBaseOfSubsingleton`: in rank zero (`Subsingleton` fibres, or
  `Module.finrank ℝ F = 0`), `S(E) = ∅` and `D(E)` is homeomorphic to `B` via the bundle
  projection;
* `Bundle.Trivialization.discBundle`: restriction of a norm-preserving local trivialization of `E`
  to a local trivialization of `discBundleProj F E` with fibre `closedBall (0 : F) 1`;
* `TauCeti.exists_trivialization_discBundleProj`, `TauCeti.isProperMap_discBundleProj`, and
  `TauCeti.closed_discBundleProj_preimage`: for a finite-rank continuous Riemannian vector bundle,
  `discBundleProj F E` is locally trivial with compact fibre `closedBall (0 : F) 1`, hence proper,
  and preserves the weak topology of any classical relative CW complex in a Hausdorff base;
* `TauCeti.radialBundleHomeomorph`, `TauCeti.discBundleRadialHomeomorph`, and
  `TauCeti.sphereBundleRadialHomeomorph`: radial rescaling `v ↦ (‖v‖₁ / ‖Φ v‖₂) • Φ v` turns any
  continuous bundle isomorphism `Φ : E₁ ≃ E₂` between finite-rank real vector bundles with
  continuous fibre norms into a fibrewise norm-preserving homeomorphism of total spaces carrying
  `D(E₁)` onto `D(E₂)` and `S(E₁)` onto `S(E₂)`, showing in particular that the homeomorphism type
  of `(D(E), S(E))` over `B` is independent of the choice of continuous fibre metric.

## References

* J. W. Milnor and J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton University Press, 1974, §9–§10.
* D. Husemoller, *Fibre Bundles*, third edition, Graduate Texts in Mathematics 20, Springer, 1994,
  Chapter 3.
-/

public section

noncomputable section

open Bundle Filter Metric Set Topology

universe w

namespace TauCeti

section Basic

variable {B : Type w} (F : Type*) (E : B → Type w) [∀ b, NormedAddCommGroup (E b)]

/-- When every fibre is a subsingleton (for instance in rank zero), the unit disc bundle is the
whole total space. -/
theorem eq_univ_discBundle_of_subsingleton [∀ b, Subsingleton (E b)] :
    discBundle F E = univ :=
  eq_univ_of_forall fun v ↦ by simp [Subsingleton.elim v.2 0]

/-- When every fibre is a subsingleton (for instance in rank zero), the unit sphere bundle is
empty. -/
theorem eq_empty_sphereBundle_of_subsingleton [∀ b, Subsingleton (E b)] :
    sphereBundle F E = ∅ :=
  eq_empty_of_forall_notMem fun v hv ↦ by
    simpa [Subsingleton.elim v.2 0] using mem_sphereBundle.1 hv

variable [TopologicalSpace (TotalSpace F E)]

/-- The unit disc bundle is closed in the total space when the fibre norm is continuous. -/
theorem isClosed_discBundle (hnorm : Continuous fun v : TotalSpace F E ↦ ‖v.2‖) :
    IsClosed (discBundle F E) := by
  have h : discBundle F E = {v | ‖v.2‖ ≤ 1} := Set.ext fun _ ↦ mem_discBundle
  exact h ▸ isClosed_le hnorm continuous_const

/-- The unit sphere bundle is closed in the total space when the fibre norm is continuous. -/
theorem isClosed_sphereBundle (hnorm : Continuous fun v : TotalSpace F E ↦ ‖v.2‖) :
    IsClosed (sphereBundle F E) := by
  have h : sphereBundle F E = {v | ‖v.2‖ = 1} := Set.ext fun _ ↦ mem_sphereBundle
  exact h ▸ isClosed_eq hnorm continuous_const

variable [TopologicalSpace B] [NormedAddCommGroup F] [FiberBundle F E]

/-- The projection `D(E) → B` of the unit disc bundle of a bundle with normed fibres. -/
def discBundleProj : C(discBundle F E, B) :=
  ⟨fun v ↦ (v : TotalSpace F E).proj,
    (FiberBundle.continuous_proj F E).comp continuous_subtype_val⟩

@[simp]
theorem discBundleProj_apply (v : discBundle F E) :
    discBundleProj F E v = (v : TotalSpace F E).proj :=
  (rfl)

/-- **Rank-zero disc bundle homeomorphism.** When the model fibre and every bundle fibre are
subsingletons, the projection `discBundleProj F E : D(E) → B` is a homeomorphism, with inverse the
zero section. -/
def discBundleHomeomorphBaseOfSubsingleton [Subsingleton F] [∀ b, Subsingleton (E b)] :
    discBundle F E ≃ₜ B where
  toFun := discBundleProj F E
  invFun b := ⟨TotalSpace.mk' F b 0, by simp⟩
  left_inv := by
    rintro ⟨⟨b, u⟩, _⟩
    exact Subtype.ext (TotalSpace.ext rfl (heq_of_eq (Subsingleton.elim 0 u)))
  right_inv _ := rfl
  continuous_toFun := (discBundleProj F E).continuous
  continuous_invFun := by
    refine Continuous.subtype_mk (continuous_iff_continuousAt.2 fun b₀ ↦ ?_) _
    rw [FiberBundle.continuousAt_totalSpace]
    exact ⟨continuousAt_id, (continuousAt_const (y := (0 : F))).congr
      (Eventually.of_forall fun _ ↦ Subsingleton.elim _ _)⟩

@[simp]
theorem discBundleHomeomorphBaseOfSubsingleton_apply [Subsingleton F] [∀ b, Subsingleton (E b)]
    (v : discBundle F E) :
    discBundleHomeomorphBaseOfSubsingleton F E v = (v : TotalSpace F E).proj :=
  (rfl)

@[simp]
theorem coe_discBundleHomeomorphBaseOfSubsingleton_symm_apply [Subsingleton F]
    [∀ b, Subsingleton (E b)] (b : B) :
    ((discBundleHomeomorphBaseOfSubsingleton F E).symm b : TotalSpace F E) =
      TotalSpace.mk' F b 0 :=
  (rfl)

/-- In rank zero (`Module.finrank ℝ F = 0` for finite-dimensional `F`), the unit sphere bundle is
empty. -/
theorem eq_empty_sphereBundle_of_finrank_eq_zero [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (hF : Module.finrank ℝ F = 0) :
    sphereBundle F E = ∅ := by
  have : Subsingleton F := Module.finrank_zero_iff.1 hF
  have (b : B) : Subsingleton (E b) := (FiberBundle.homeomorphAt F E b).injective.subsingleton
  exact eq_empty_sphereBundle_of_subsingleton F E

/-- In rank zero (`Module.finrank ℝ F = 0` for finite-dimensional `F`), the unit disc bundle is
homeomorphic to the base `B` via the bundle projection. -/
def discBundleHomeomorphBaseOfFinrankZero [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (hF : Module.finrank ℝ F = 0) :
    discBundle F E ≃ₜ B :=
  have : Subsingleton F := Module.finrank_zero_iff.1 hF
  have (b : B) : Subsingleton (E b) := (FiberBundle.homeomorphAt F E b).injective.subsingleton
  discBundleHomeomorphBaseOfSubsingleton F E

end Basic

end TauCeti

namespace Bundle.Trivialization

open TauCeti

variable {B : Type w} [TopologicalSpace B] {F : Type*} [NormedAddCommGroup F]
  {E : B → Type w} [TopologicalSpace (TotalSpace F E)] [∀ b, NormedAddCommGroup (E b)]
  [FiberBundle F E]

open Classical in
/-- Restrict a fibrewise norm-preserving local trivialization `e` of `E` to a local trivialization
of `discBundleProj F E : D(E) → B` with model fibre `closedBall (0 : F) 1`. -/
def discBundle (e : Trivialization F (π F E))
    (he : ∀ b ∈ e.baseSet, ∀ v : E b, ‖(e ⟨b, v⟩).2‖ = ‖v‖) :
    Trivialization (closedBall (0 : F) 1) (discBundleProj F E) where
  toFun v := (v.1.proj,
    if hb : v.1.proj ∈ e.baseSet then
      ⟨(e v.1).2,
        mem_closedBall_zero_iff.2 ((he v.1.proj hb v.1.2).trans_le (mem_discBundle.1 v.2))⟩
    else ⟨0, mem_closedBall_self zero_le_one⟩)
  invFun p :=
    if hb : p.1 ∈ e.baseSet then
      ⟨e.toOpenPartialHomeomorph.symm (p.1, p.2.1), by
        have hproj : (e.toOpenPartialHomeomorph.symm (p.1, p.2.1)).proj = p.1 :=
          e.proj_symm_apply' hb
        have happ : e (e.toOpenPartialHomeomorph.symm (p.1, p.2.1)) = (p.1, p.2.1) :=
          e.apply_symm_apply (e.mem_target.2 hb)
        have hiso := he _ (hproj.symm ▸ hb) (e.toOpenPartialHomeomorph.symm (p.1, p.2.1)).2
        rw [mem_discBundle, ← hiso, happ]
        exact mem_closedBall_zero_iff.1 p.2.2⟩
    else ⟨TotalSpace.mk' F p.1 0, by simp⟩
  source := discBundleProj F E ⁻¹' e.baseSet
  target := e.baseSet ×ˢ univ
  map_source' v hv := ⟨hv, mem_univ _⟩
  map_target' p hp := by
    rw [mem_preimage, discBundleProj_apply, dite_eq_left hp.1]
    exact (e.proj_symm_apply' hp.1).symm ▸ hp.1
  left_inv' v hv := by
    have hv' : (v : TotalSpace F E).proj ∈ e.baseSet := hv
    apply Subtype.ext
    dsimp only
    rw [dite_eq_left hv', dite_eq_left hv']
    change e.toOpenPartialHomeomorph.symm (v.1.proj, (e v.1).2) = v.1
    rw [← e.coe_fst (e.mem_source.2 hv'), Prod.mk.eta]
    exact e.left_inv (e.mem_source.2 hv')
  right_inv' p hp := by
    ext
    · dsimp only
      rw [dite_eq_left hp.1]
      exact e.proj_symm_apply' hp.1
    · dsimp only
      rw [dite_eq_left hp.1, dite_eq_left (by rw [e.proj_symm_apply' hp.1]; exact hp.1)]
      change (e (e.toOpenPartialHomeomorph.symm (p.1, p.2.1))).2 = p.2.1
      rw [e.apply_symm_apply (e.mem_target.2 hp.1)]
  open_source := e.open_baseSet.preimage (discBundleProj F E).continuous
  open_target := e.open_baseSet.prod isOpen_univ
  continuousOn_toFun := by
    refine (discBundleProj F E).continuous.continuousOn.prodMk ?_
    rw [Topology.IsInducing.subtypeVal.continuousOn_iff]
    refine (continuous_snd.comp_continuousOn <|
      e.continuousOn.comp continuous_subtype_val.continuousOn
        fun v hv ↦ e.mem_source.2 hv).congr fun v hv ↦ ?_
    have hv' : (v : TotalSpace F E).proj ∈ e.baseSet := hv
    dsimp only [Function.comp_apply]
    rw [dite_eq_left hv']
  continuousOn_invFun := by
    rw [Topology.IsInducing.subtypeVal.continuousOn_iff]
    refine (e.toOpenPartialHomeomorph.continuousOn_symm.comp
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)).continuousOn
      fun p (hp : p ∈ e.baseSet ×ˢ univ) ↦ e.mem_target.2 hp.1).congr fun p hp ↦ ?_
    dsimp only [Function.comp_apply]
    rw [dite_eq_left hp.1]
  baseSet := e.baseSet
  open_baseSet := e.open_baseSet
  source_eq := rfl
  target_eq := rfl
  proj_toFun _ _ := rfl

@[simp]
theorem discBundle_baseSet (e : Trivialization F (π F E))
    (he : ∀ b ∈ e.baseSet, ∀ v : E b, ‖(e ⟨b, v⟩).2‖ = ‖v‖) :
    (e.discBundle he).baseSet = e.baseSet :=
  (rfl)

open Classical in
@[simp]
theorem coe_discBundle_apply_snd (e : Trivialization F (π F E))
    (he : ∀ b ∈ e.baseSet, ∀ v : E b, ‖(e ⟨b, v⟩).2‖ = ‖v‖)
    {v : TauCeti.discBundle F E} (hv : (v : TotalSpace F E).proj ∈ e.baseSet) :
    ((e.discBundle he v).2 : F) = (e v.1).2 := by
  change Subtype.val (if hb : v.1.proj ∈ e.baseSet then _ else _) = (e v.1).2
  rw [dite_eq_left hv]

end Bundle.Trivialization

namespace TauCeti

section Proper

variable {B : Type w} [TopologicalSpace B]
  (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  (E : B → Type w) [TopologicalSpace (TotalSpace F E)]
  [∀ b, NormedAddCommGroup (E b)] [∀ b, InnerProductSpace ℝ (E b)]
  [FiberBundle F E] [VectorBundle ℝ F E] [IsContinuousRiemannianBundle F E]

/-- Around every point of the base, `discBundleProj F E : D(E) → B` has a local trivialization with
model fibre `closedBall (0 : F) 1`. -/
theorem exists_trivialization_discBundleProj (b : B) :
    ∃ e : Trivialization (closedBall (0 : F) 1) (discBundleProj F E), b ∈ e.baseSet := by
  obtain ⟨e, _, hb, hiso⟩ :=
    OrthonormalBasis.exists_orthonormal_trivialization (E := E) (stdOrthonormalBasis ℝ F) b
  exact ⟨e.discBundle hiso, hb⟩

/-- **The unit disc bundle projection of a finite-rank continuous Riemannian bundle is proper.** -/
theorem isProperMap_discBundleProj : IsProperMap (discBundleProj F E) :=
  have : CompactSpace (closedBall (0 : F) 1) :=
    isCompact_iff_compactSpace.1 (isCompact_closedBall _ _)
  isProperMap_of_forall_exists_trivialization (exists_trivialization_discBundleProj F E)

/-- **Weak topology of a unit disc bundle over a relative CW complex.** For a finite-rank continuous
Riemannian bundle `E → B` over a Hausdorff space `B` and a classical relative CW complex `(C, D)` in
`B`, a subset `S ⊆ D(E)|_C` is closed in `D(E)` if and only if its intersections with `D(E)|_K` for
every closed cell `K` of `C` and with `D(E)|_D` are closed. -/
theorem closed_discBundleProj_preimage [T2Space B] (C : Set B) {D : Set B} [RelCWComplex C D]
    (S : Set (discBundle F E)) (hS : S ⊆ discBundleProj F E ⁻¹' C) :
    IsClosed S ↔
      (∀ n (j : RelCWComplex.cell C n),
        IsClosed (S ∩ discBundleProj F E ⁻¹' RelCWComplex.closedCell n j)) ∧
      IsClosed (S ∩ discBundleProj F E ⁻¹' D) :=
  have : CompactSpace (closedBall (0 : F) 1) :=
    isCompact_iff_compactSpace.1 (isCompact_closedBall _ _)
  RelCWComplex.closed_of_forall_exists_trivialization
    (exists_trivialization_discBundleProj F E) C S hS

end Proper

section RadialMetricChange

section Algebraic

variable {B : Type*} (F₁ F₂ : Type*) {E₁ : B → Type*} {E₂ : B → Type*}
  [∀ b, NormedAddCommGroup (E₁ b)] [∀ b, NormedSpace ℝ (E₁ b)]
  [∀ b, NormedAddCommGroup (E₂ b)] [∀ b, NormedSpace ℝ (E₂ b)]

/-- Radial rescaling of a family of fibrewise linear equivalences `Φ b : E₁ b ≃L[ℝ] E₂ b`: sends
`v` over `b` to `(‖v‖ / ‖Φ b v‖) • Φ b v` (which is `0` when `v = 0`). -/
def radialBundleMap (Φ : ∀ b, E₁ b ≃L[ℝ] E₂ b) (v : TotalSpace F₁ E₁) : TotalSpace F₂ E₂ :=
  TotalSpace.mk' F₂ v.proj ((‖v.2‖ / ‖Φ v.proj v.2‖) • Φ v.proj v.2)

@[simp]
theorem radialBundleMap_mk (Φ : ∀ b, E₁ b ≃L[ℝ] E₂ b) (b : B) (u : E₁ b) :
    radialBundleMap F₁ F₂ Φ ⟨b, u⟩ = ⟨b, (‖u‖ / ‖Φ b u‖) • Φ b u⟩ :=
  (rfl)

@[simp]
theorem radialBundleMap_proj (Φ : ∀ b, E₁ b ≃L[ℝ] E₂ b) (v : TotalSpace F₁ E₁) :
    (radialBundleMap F₁ F₂ Φ v).proj = v.proj :=
  (rfl)

theorem radialBundleMap_zero (Φ : ∀ b, E₁ b ≃L[ℝ] E₂ b) (b : B) :
    radialBundleMap F₁ F₂ Φ (TotalSpace.mk' F₁ b 0) = TotalSpace.mk' F₂ b 0 := by
  simp [TotalSpace.mk']

/-- Radial rescaling preserves the fibre norm identically. -/
@[simp]
theorem norm_radialBundleMap (Φ : ∀ b, E₁ b ≃L[ℝ] E₂ b) (v : TotalSpace F₁ E₁) :
    ‖(radialBundleMap F₁ F₂ Φ v).2‖ = ‖v.2‖ := by
  rcases v with ⟨b, u⟩
  rw [radialBundleMap_mk]
  dsimp only
  by_cases hu : u = 0
  · simp [hu]
  · have hΦu : Φ b u ≠ 0 := (map_ne_zero_iff _ (Φ b).injective).2 hu
    rw [norm_smul, Real.norm_of_nonneg (by positivity),
      div_mul_cancel₀ _ (norm_ne_zero_iff.2 hΦu)]

/-- Radial rescaling of `(Φ b).symm` is the two-sided inverse of radial rescaling of `Φ b`. -/
@[simp]
theorem radialBundleMap_symm_apply (Φ : ∀ b, E₁ b ≃L[ℝ] E₂ b) (v : TotalSpace F₁ E₁) :
    radialBundleMap F₂ F₁ (fun b ↦ (Φ b).symm) (radialBundleMap F₁ F₂ Φ v) = v := by
  rcases v with ⟨b, u⟩
  rw [radialBundleMap_mk, radialBundleMap_mk]
  congr 1
  by_cases hu : u = 0
  · simp [hu]
  · have hΦu : Φ b u ≠ 0 := (map_ne_zero_iff _ (Φ b).injective).2 hu
    have hc : 0 < ‖u‖ / ‖Φ b u‖ := div_pos (norm_pos_iff.2 hu) (norm_pos_iff.2 hΦu)
    rw [map_smul, ContinuousLinearEquiv.symm_apply_apply, norm_smul, norm_smul,
      Real.norm_of_nonneg hc.le, div_mul_cancel₀ _ (norm_ne_zero_iff.2 hΦu),
      smul_smul, div_mul_eq_div_div_swap, div_self (norm_ne_zero_iff.2 hu), one_div,
      inv_mul_cancel₀ hc.ne', one_smul]

end Algebraic

section TotalSpace

variable {B : Type*} [TopologicalSpace B]
  (F₁ F₂ : Type*) [NormedAddCommGroup F₁] [NormedSpace ℝ F₁]
  [NormedAddCommGroup F₂] [NormedSpace ℝ F₂]
  {E₁ : B → Type*} {E₂ : B → Type*}
  [TopologicalSpace (TotalSpace F₁ E₁)] [TopologicalSpace (TotalSpace F₂ E₂)]
  [∀ b, NormedAddCommGroup (E₁ b)] [∀ b, NormedSpace ℝ (E₁ b)]
  [∀ b, NormedAddCommGroup (E₂ b)] [∀ b, NormedSpace ℝ (E₂ b)]
  [FiberBundle F₁ E₁] [VectorBundle ℝ F₁ E₁]
  [FiberBundle F₂ E₂] [VectorBundle ℝ F₂ E₂]

omit [TopologicalSpace B] [NormedAddCommGroup F₁] [NormedSpace ℝ F₁] [NormedAddCommGroup F₂]
  [NormedSpace ℝ F₂] [TopologicalSpace (TotalSpace F₁ E₁)] [TopologicalSpace (TotalSpace F₂ E₂)]
  [∀ b, NormedAddCommGroup (E₁ b)] [∀ b, NormedSpace ℝ (E₁ b)]
  [∀ b, NormedAddCommGroup (E₂ b)] [∀ b, NormedSpace ℝ (E₂ b)]
  [FiberBundle F₁ E₁] [VectorBundle ℝ F₁ E₁] [FiberBundle F₂ E₂] [VectorBundle ℝ F₂ E₂] in
private lemma exists_lt_mul_on_singleton_prod_univ {α β : Type*} [TopologicalSpace α]
    [TopologicalSpace β] [CompactSpace β] (a₀ : α) {φ₁ φ₂ : α × β → ℝ}
    (hφ₁ : Continuous φ₁) (hφ₂ : Continuous φ₂) (hpos : ∀ y : β, 0 < φ₂ (a₀, y)) :
    ∃ C : ℝ, 0 ≤ C ∧ ({a₀} ×ˢ (univ : Set β)) ⊆ {q | φ₁ q < C * φ₂ q} := by
  let K : Set (α × β) := {a₀} ×ˢ univ
  have hKc : IsCompact K := isCompact_singleton.prod isCompact_univ
  rcases isEmpty_or_nonempty β with hE | hNE
  · exact ⟨0, le_rfl, fun q _ ↦ hE.elim q.2⟩
  · have hKne : K.Nonempty := (singleton_nonempty _).prod univ_nonempty
    obtain ⟨q₁, -, hq₁⟩ := hKc.exists_isMaxOn hKne hφ₁.continuousOn
    obtain ⟨q₂, hq₂K, hq₂⟩ := hKc.exists_isMinOn hKne hφ₂.continuousOn
    have hpos₂ : 0 < φ₂ q₂ := by
      obtain ⟨hq₂1, -⟩ := mem_prod.1 hq₂K
      rw [mem_singleton_iff] at hq₂1
      rw [← Prod.eta q₂, hq₂1]
      exact hpos q₂.2
    refine ⟨(max (φ₁ q₁) 0 + 1) / φ₂ q₂, by positivity, fun q hq ↦ ?_⟩
    change φ₁ q < _
    calc φ₁ q ≤ max (φ₁ q₁) 0 := (hq₁ hq).trans (le_max_left _ _)
      _ < max (φ₁ q₁) 0 + 1 := lt_add_one _
      _ = ((max (φ₁ q₁) 0 + 1) / φ₂ q₂) * φ₂ q₂ := (div_mul_cancel₀ _ hpos₂.ne').symm
      _ ≤ ((max (φ₁ q₁) 0 + 1) / φ₂ q₂) * φ₂ q :=
        mul_le_mul_of_nonneg_left (hq₂ hq) (by positivity)

omit [NormedAddCommGroup F₁] [NormedSpace ℝ F₁] [FiberBundle F₁ E₁] [VectorBundle ℝ F₁ E₁] in
/-- Near any base point `b₀`, the radial distortion `‖u‖ / ‖Φ b u‖` is uniformly bounded on fibres
over a neighbourhood of `b₀`. -/
private lemma exists_nhds_radial_ratio_le [FiniteDimensional ℝ F₂] (Φ : ∀ b, E₁ b ≃L[ℝ] E₂ b)
    (hnorm₁ : Continuous fun v : TotalSpace F₁ E₁ ↦ ‖v.2‖)
    (hnorm₂ : Continuous fun w : TotalSpace F₂ E₂ ↦ ‖w.2‖)
    (hΦ_symm : Continuous fun w : TotalSpace F₂ E₂ ↦ TotalSpace.mk' F₁ w.proj ((Φ w.proj).symm w.2))
    (b₀ : B) :
    ∃ U ∈ 𝓝 b₀, ∃ C : ℝ, 0 ≤ C ∧ ∀ (b : B), b ∈ U → ∀ u : E₁ b, ‖u‖ / ‖Φ b u‖ ≤ C := by
  let e₂ := trivializationAt F₂ E₂ b₀
  have hb₀ : b₀ ∈ e₂.baseSet := mem_baseSet_trivializationAt F₂ E₂ b₀
  let g : e₂.baseSet × sphere (0 : F₂) 1 → TotalSpace F₂ E₂ :=
    fun q ↦ TotalSpace.mk' F₂ q.1.1 (e₂.symmL ℝ q.1.1 q.2.1)
  have hg : Continuous g :=
    (e₂.continuousOn_symm.comp_continuous
      ((continuous_subtype_val.comp continuous_fst).prodMk
        (continuous_subtype_val.comp continuous_snd))
      fun q ↦ ⟨q.1.2, mem_univ _⟩).congr fun q ↦ by simp [g]
  let φ₁ : e₂.baseSet × sphere (0 : F₂) 1 → ℝ := fun q ↦ ‖(Φ q.1.1).symm (g q).2‖
  let φ₂ : e₂.baseSet × sphere (0 : F₂) 1 → ℝ := fun q ↦ ‖(g q).2‖
  have hφ₁ : Continuous φ₁ := hnorm₁.comp (hΦ_symm.comp hg)
  have hφ₂ : Continuous φ₂ := hnorm₂.comp hg
  have hφ₂_pos (y : sphere (0 : F₂) 1) : 0 < φ₂ (⟨b₀, hb₀⟩, y) := by
    refine norm_pos_iff.2 fun h0 ↦ ?_
    have hy : (y : F₂) = 0 := by
      rw [← e₂.continuousLinearMapAt_symmL (R := ℝ) hb₀ y.1,
        show e₂.symmL ℝ b₀ y.1 = 0 from h0, map_zero]
    have hmem := y.2
    rw [mem_sphere_zero_iff_norm, hy, norm_zero] at hmem
    exact zero_ne_one hmem
  have : CompactSpace (sphere (0 : F₂) 1) := isCompact_iff_compactSpace.1 (isCompact_sphere 0 1)
  obtain ⟨C, hC₀, hKC⟩ :=
    exists_lt_mul_on_singleton_prod_univ (⟨b₀, hb₀⟩ : e₂.baseSet) hφ₁ hφ₂ hφ₂_pos
  obtain ⟨V, W, hVo, -, hb₀V, hKW, hVW⟩ := generalized_tube_lemma isCompact_singleton isCompact_univ
    (isOpen_lt hφ₁ (continuous_const.mul hφ₂)) hKC
  refine ⟨Subtype.val '' V, (e₂.open_baseSet.isOpenMap_subtype_val V hVo).mem_nhds
    ⟨⟨b₀, hb₀⟩, hb₀V (mem_singleton _), rfl⟩, C, hC₀, ?_⟩
  rintro _ ⟨⟨b, hb⟩, hbV, rfl⟩ u
  by_cases hu : u = 0
  · simp [hu, hC₀]
  · set w : E₂ b := Φ b u
    have hw : w ≠ 0 := (map_ne_zero_iff _ (Φ b).injective).2 hu
    set z : F₂ := e₂.continuousLinearMapAt ℝ b w
    have hzw : e₂.symmL ℝ b z = w := e₂.symmL_continuousLinearMapAt hb w
    have hz : z ≠ 0 := fun hz0 ↦ hw (by rw [← hzw, hz0, map_zero])
    let y : sphere (0 : F₂) 1 := ⟨‖z‖⁻¹ • z, by simp [norm_smul, norm_ne_zero_iff.2 hz]⟩
    have hlt : φ₁ (⟨b, hb⟩, y) < C * φ₂ (⟨b, hb⟩, y) := hVW ⟨hbV, hKW (mem_univ y)⟩
    have hgy : (g (⟨b, hb⟩, y)).2 = ‖z‖⁻¹ • w := by simp [g, y, map_smul, hzw]
    have hpos_z : 0 < ‖z‖⁻¹ := inv_pos.2 (norm_pos_iff.2 hz)
    dsimp only [φ₁, φ₂] at hlt
    rw [hgy, map_smul, ContinuousLinearEquiv.symm_apply_apply, norm_smul, norm_smul,
      Real.norm_of_nonneg hpos_z.le, mul_left_comm C, mul_lt_mul_iff_right₀ hpos_z] at hlt
    exact (div_le_iff₀ (norm_pos_iff.2 hw)).2 hlt.le

omit [NormedSpace ℝ F₁] [VectorBundle ℝ F₁ E₁] in
/-- **Continuity of radial bundle rescaling.** Rescaling a continuous bundle isomorphism
`Φ : E₁ ≃ E₂` fibrewise by `‖v‖ / ‖Φ v‖` is continuous whenever both bundles have continuous fibre
norms and `F₂` is finite-dimensional. -/
theorem continuous_radialBundleMap [FiniteDimensional ℝ F₂] (Φ : ∀ b, E₁ b ≃L[ℝ] E₂ b)
    (hnorm₁ : Continuous fun v : TotalSpace F₁ E₁ ↦ ‖v.2‖)
    (hnorm₂ : Continuous fun w : TotalSpace F₂ E₂ ↦ ‖w.2‖)
    (hΦ : Continuous fun v : TotalSpace F₁ E₁ ↦ TotalSpace.mk' F₂ v.proj (Φ v.proj v.2))
    (hΦ_symm : Continuous fun w : TotalSpace F₂ E₂ ↦
      TotalSpace.mk' F₁ w.proj ((Φ w.proj).symm w.2)) :
    Continuous (radialBundleMap F₁ F₂ Φ) := by
  refine continuous_iff_continuousAt.2 fun v₀ ↦ ?_
  obtain ⟨U, hU, C, -, hbound⟩ :=
    exists_nhds_radial_ratio_le F₁ F₂ Φ hnorm₁ hnorm₂ hΦ_symm v₀.proj
  obtain ⟨V, hVU, hVo, hb₀V⟩ := mem_nhds_iff.1 hU
  let W : Set (TotalSpace F₁ E₁) := π F₁ E₁ ⁻¹' V
  have hWo : IsOpen W := hVo.preimage (FiberBundle.continuous_proj F₁ E₁)
  have hsub : Continuous (W.domRestrict (radialBundleMap F₁ F₂ Φ)) := by
    refine Continuous.smul_totalSpace_of_norm_le (C := C)
      (φ := fun v : W ↦ TotalSpace.mk' F₂ v.1.proj (Φ v.1.proj v.1.2))
      (c := fun v : W ↦ ‖v.1.2‖ / ‖Φ v.1.proj v.1.2‖) (hΦ.comp continuous_subtype_val)
      (fun v ↦ ?_) (fun v hv ↦ ?_)
    · rw [Real.norm_of_nonneg (by positivity)]
      exact hbound v.1.proj (hVU v.2) v.1.2
    · exact (hnorm₁.comp continuous_subtype_val).continuousAt.div
        (hnorm₂.comp (hΦ.comp continuous_subtype_val)).continuousAt (norm_ne_zero_iff.2 hv)
  exact (continuousOn_iff_continuous_domRestrict.2 hsub).continuousAt (hWo.mem_nhds hb₀V)

/-- **Metric-change radial bundle homeomorphism.** Given two finite-rank real vector bundles `E₁`
and `E₂` over `B` with continuous fibre norms and a continuous bundle isomorphism `Φ : E₁ ≃ E₂`,
radial rescaling `v ↦ (‖v‖ / ‖Φ v‖) • Φ v` is a homeomorphism `TotalSpace F₁ E₁ ≃ₜ TotalSpace F₂ E₂`
covering the identity of `B` and preserving norms on every fibre. -/
def radialBundleHomeomorph [FiniteDimensional ℝ F₁] [FiniteDimensional ℝ F₂]
    (Φ : ∀ b, E₁ b ≃L[ℝ] E₂ b)
    (hnorm₁ : Continuous fun v : TotalSpace F₁ E₁ ↦ ‖v.2‖)
    (hnorm₂ : Continuous fun w : TotalSpace F₂ E₂ ↦ ‖w.2‖)
    (hΦ : Continuous fun v : TotalSpace F₁ E₁ ↦ TotalSpace.mk' F₂ v.proj (Φ v.proj v.2))
    (hΦ_symm : Continuous fun w : TotalSpace F₂ E₂ ↦
      TotalSpace.mk' F₁ w.proj ((Φ w.proj).symm w.2)) :
    TotalSpace F₁ E₁ ≃ₜ TotalSpace F₂ E₂ where
  toFun := radialBundleMap F₁ F₂ Φ
  invFun := radialBundleMap F₂ F₁ fun b ↦ (Φ b).symm
  left_inv := radialBundleMap_symm_apply F₁ F₂ Φ
  right_inv := radialBundleMap_symm_apply F₂ F₁ fun b ↦ (Φ b).symm
  continuous_toFun := continuous_radialBundleMap F₁ F₂ Φ hnorm₁ hnorm₂ hΦ hΦ_symm
  continuous_invFun :=
    continuous_radialBundleMap F₂ F₁ (fun b ↦ (Φ b).symm) hnorm₂ hnorm₁ hΦ_symm hΦ

@[simp]
theorem radialBundleHomeomorph_apply [FiniteDimensional ℝ F₁] [FiniteDimensional ℝ F₂]
    (Φ : ∀ b, E₁ b ≃L[ℝ] E₂ b)
    (hnorm₁ : Continuous fun v : TotalSpace F₁ E₁ ↦ ‖v.2‖)
    (hnorm₂ : Continuous fun w : TotalSpace F₂ E₂ ↦ ‖w.2‖)
    (hΦ : Continuous fun v : TotalSpace F₁ E₁ ↦ TotalSpace.mk' F₂ v.proj (Φ v.proj v.2))
    (hΦ_symm : Continuous fun w : TotalSpace F₂ E₂ ↦
      TotalSpace.mk' F₁ w.proj ((Φ w.proj).symm w.2))
    (v : TotalSpace F₁ E₁) :
    radialBundleHomeomorph F₁ F₂ Φ hnorm₁ hnorm₂ hΦ hΦ_symm v = radialBundleMap F₁ F₂ Φ v :=
  (rfl)

@[simp]
theorem radialBundleHomeomorph_symm_apply [FiniteDimensional ℝ F₁] [FiniteDimensional ℝ F₂]
    (Φ : ∀ b, E₁ b ≃L[ℝ] E₂ b)
    (hnorm₁ : Continuous fun v : TotalSpace F₁ E₁ ↦ ‖v.2‖)
    (hnorm₂ : Continuous fun w : TotalSpace F₂ E₂ ↦ ‖w.2‖)
    (hΦ : Continuous fun v : TotalSpace F₁ E₁ ↦ TotalSpace.mk' F₂ v.proj (Φ v.proj v.2))
    (hΦ_symm : Continuous fun w : TotalSpace F₂ E₂ ↦
      TotalSpace.mk' F₁ w.proj ((Φ w.proj).symm w.2))
    (w : TotalSpace F₂ E₂) :
    (radialBundleHomeomorph F₁ F₂ Φ hnorm₁ hnorm₂ hΦ hΦ_symm).symm w =
      radialBundleMap F₂ F₁ (fun b ↦ (Φ b).symm) w :=
  (rfl)

end TotalSpace

section Subbundles

variable {B : Type w} [TopologicalSpace B]
  (F₁ F₂ : Type*) [NormedAddCommGroup F₁] [NormedSpace ℝ F₁] [FiniteDimensional ℝ F₁]
  [NormedAddCommGroup F₂] [NormedSpace ℝ F₂] [FiniteDimensional ℝ F₂]
  {E₁ : B → Type w} {E₂ : B → Type w}
  [TopologicalSpace (TotalSpace F₁ E₁)] [TopologicalSpace (TotalSpace F₂ E₂)]
  [∀ b, NormedAddCommGroup (E₁ b)] [∀ b, NormedSpace ℝ (E₁ b)]
  [∀ b, NormedAddCommGroup (E₂ b)] [∀ b, NormedSpace ℝ (E₂ b)]
  [FiberBundle F₁ E₁] [VectorBundle ℝ F₁ E₁]
  [FiberBundle F₂ E₂] [VectorBundle ℝ F₂ E₂]

/-- **Metric-change radial homeomorphism of unit disc bundles.** -/
def discBundleRadialHomeomorph (Φ : ∀ b, E₁ b ≃L[ℝ] E₂ b)
    (hnorm₁ : Continuous fun v : TotalSpace F₁ E₁ ↦ ‖v.2‖)
    (hnorm₂ : Continuous fun w : TotalSpace F₂ E₂ ↦ ‖w.2‖)
    (hΦ : Continuous fun v : TotalSpace F₁ E₁ ↦ TotalSpace.mk' F₂ v.proj (Φ v.proj v.2))
    (hΦ_symm : Continuous fun w : TotalSpace F₂ E₂ ↦
      TotalSpace.mk' F₁ w.proj ((Φ w.proj).symm w.2)) :
    discBundle F₁ E₁ ≃ₜ discBundle F₂ E₂ where
  toFun v := ⟨radialBundleMap F₁ F₂ Φ v.1,
    mem_discBundle.2 ((norm_radialBundleMap F₁ F₂ Φ v.1).trans_le (mem_discBundle.1 v.2))⟩
  invFun w := ⟨radialBundleMap F₂ F₁ (fun b ↦ (Φ b).symm) w.1,
    mem_discBundle.2 ((norm_radialBundleMap F₂ F₁ _ w.1).trans_le (mem_discBundle.1 w.2))⟩
  left_inv v := Subtype.ext (radialBundleMap_symm_apply F₁ F₂ Φ v.1)
  right_inv w := Subtype.ext (radialBundleMap_symm_apply F₂ F₁ (fun b ↦ (Φ b).symm) w.1)
  continuous_toFun :=
    ((continuous_radialBundleMap F₁ F₂ Φ hnorm₁ hnorm₂ hΦ hΦ_symm).comp
      continuous_subtype_val).subtype_mk _
  continuous_invFun :=
    ((continuous_radialBundleMap F₂ F₁ (fun b ↦ (Φ b).symm) hnorm₂ hnorm₁ hΦ_symm hΦ).comp
      continuous_subtype_val).subtype_mk _

@[simp]
theorem coe_discBundleRadialHomeomorph_apply (Φ : ∀ b, E₁ b ≃L[ℝ] E₂ b)
    (hnorm₁ : Continuous fun v : TotalSpace F₁ E₁ ↦ ‖v.2‖)
    (hnorm₂ : Continuous fun w : TotalSpace F₂ E₂ ↦ ‖w.2‖)
    (hΦ : Continuous fun v : TotalSpace F₁ E₁ ↦ TotalSpace.mk' F₂ v.proj (Φ v.proj v.2))
    (hΦ_symm : Continuous fun w : TotalSpace F₂ E₂ ↦
      TotalSpace.mk' F₁ w.proj ((Φ w.proj).symm w.2))
    (v : discBundle F₁ E₁) :
    (discBundleRadialHomeomorph F₁ F₂ Φ hnorm₁ hnorm₂ hΦ hΦ_symm v : TotalSpace F₂ E₂) =
      radialBundleMap F₁ F₂ Φ v.1 :=
  (rfl)

/-- **Metric-change radial homeomorphism of unit sphere bundles.** -/
def sphereBundleRadialHomeomorph (Φ : ∀ b, E₁ b ≃L[ℝ] E₂ b)
    (hnorm₁ : Continuous fun v : TotalSpace F₁ E₁ ↦ ‖v.2‖)
    (hnorm₂ : Continuous fun w : TotalSpace F₂ E₂ ↦ ‖w.2‖)
    (hΦ : Continuous fun v : TotalSpace F₁ E₁ ↦ TotalSpace.mk' F₂ v.proj (Φ v.proj v.2))
    (hΦ_symm : Continuous fun w : TotalSpace F₂ E₂ ↦
      TotalSpace.mk' F₁ w.proj ((Φ w.proj).symm w.2)) :
    sphereBundle F₁ E₁ ≃ₜ sphereBundle F₂ E₂ where
  toFun v := ⟨radialBundleMap F₁ F₂ Φ v.1,
    mem_sphereBundle.2 ((norm_radialBundleMap F₁ F₂ Φ v.1).trans (mem_sphereBundle.1 v.2))⟩
  invFun w := ⟨radialBundleMap F₂ F₁ (fun b ↦ (Φ b).symm) w.1,
    mem_sphereBundle.2 ((norm_radialBundleMap F₂ F₁ _ w.1).trans (mem_sphereBundle.1 w.2))⟩
  left_inv v := Subtype.ext (radialBundleMap_symm_apply F₁ F₂ Φ v.1)
  right_inv w := Subtype.ext (radialBundleMap_symm_apply F₂ F₁ (fun b ↦ (Φ b).symm) w.1)
  continuous_toFun :=
    ((continuous_radialBundleMap F₁ F₂ Φ hnorm₁ hnorm₂ hΦ hΦ_symm).comp
      continuous_subtype_val).subtype_mk _
  continuous_invFun :=
    ((continuous_radialBundleMap F₂ F₁ (fun b ↦ (Φ b).symm) hnorm₂ hnorm₁ hΦ_symm hΦ).comp
      continuous_subtype_val).subtype_mk _

@[simp]
theorem coe_sphereBundleRadialHomeomorph_apply (Φ : ∀ b, E₁ b ≃L[ℝ] E₂ b)
    (hnorm₁ : Continuous fun v : TotalSpace F₁ E₁ ↦ ‖v.2‖)
    (hnorm₂ : Continuous fun w : TotalSpace F₂ E₂ ↦ ‖w.2‖)
    (hΦ : Continuous fun v : TotalSpace F₁ E₁ ↦ TotalSpace.mk' F₂ v.proj (Φ v.proj v.2))
    (hΦ_symm : Continuous fun w : TotalSpace F₂ E₂ ↦
      TotalSpace.mk' F₁ w.proj ((Φ w.proj).symm w.2))
    (v : sphereBundle F₁ E₁) :
    (sphereBundleRadialHomeomorph F₁ F₂ Φ hnorm₁ hnorm₂ hΦ hΦ_symm v : TotalSpace F₂ E₂) =
      radialBundleMap F₁ F₂ Φ v.1 :=
  (rfl)

end Subbundles

end RadialMetricChange

end TauCeti
