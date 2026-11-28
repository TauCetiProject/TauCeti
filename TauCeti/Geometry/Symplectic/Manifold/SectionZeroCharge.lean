/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.VectorBundle.Basic
public import TauCeti.Geometry.Symplectic.Manifold.ZeroCharge
import TauCeti.Topology.UnitInterval.Contractible
import TauCeti.Topology.VectorBundle.Contractible

/-!
# The zero charges of discs for a section of a complex line bundle

Let `E` be a complex line bundle over a space `Y`, and let `α : Y → E` be a continuous map to its
total space, for instance a section, such as the framing section of a Hermitian line on a
four-manifold. A continuous disc `σ : 𝔻 → Y` meets the zero set
`Z = {y | α y = 0 in its fibre}` in `σ⁻¹(Z)`. Since `𝔻` is contractible, `E` has a continuous frame
`φ z : ℂ ≃ E_(π (α (σ z)))` along `σ`, and in such a frame `α ∘ σ` is a continuous function
`c : 𝔻 → ℂ`, `α (σ z) = φ z (c z)`. The **zero charge** `ContinuousMap.sectionZeroCharge α σ` is the
zero charge of the disc `c` in `ℂ` (`ContinuousMap.zeroCharge`): the number of zeros of `α ∘ σ`,
counted with their topological multiplicities.

It does not depend on the frame (`ContinuousMap.sectionZeroCharge_eq_zeroCharge`). Two frames
differ by a continuous nonvanishing function `a : 𝔻 → ℂ`, which changes the coordinate `c` into
`a * c`, and the zero charge is invariant under such gauge changes
(`ContinuousMap.zeroCharge_mul_left`). In particular, when `σ` lands in the base set of a linear
trivialization `e` of `E`, the zero charge is that of the coordinate function
`z ↦ (e (α (σ z))).2` of `α ∘ σ` in `e`
(`ContinuousMap.sectionZeroCharge_eq_zeroCharge_of_mem_baseSet`). So in a local trivialization,
where the framing section is a function `Y → ℂ`, it is the framed charge of the flat chart, the
winding number of `α ∘ σ` along a circle enclosing its zeros
(`ContinuousMap.zeroCharge_eq_degree_toBasedLoop`). For the same reason the zero charge does not
change when `α` is multiplied by a continuous function that vanishes nowhere along `σ`, for instance
a unitary gauge transformation (`ContinuousMap.sectionZeroCharge_eq_of_eq_smul`).

When `σ⁻¹(Z)` is compact, the zero charges obey, for every continuous `α`, the laws of a positive
cohomology assignment (`TauCeti.PositiveCohomologyAssignment`) other than positivity:

* **vacuum**: the zero charge vanishes when `σ` misses `Z`
  (`ContinuousMap.sectionZeroCharge_eq_zero_of_forall_ne_zero`);
* **homotopy**: it is constant along a homotopy whose total preimage of `Z` is compact
  (`ContinuousMap.sectionZeroCharge_eq_of_homotopy`);
* **degree**: it multiplies by the degree of a proper reparametrization `θ : 𝔻 → 𝔻`
  (`ContinuousMap.sectionZeroCharge_comp`);
* **additivity**: it is the sum of the zero charges of finitely many disjoint round subdiscs
  containing `σ⁻¹(Z)` (`ContinuousMap.sectionZeroCharge_eq_sum`).

Each law is the law of `ContinuousMap.zeroCharge` for the coordinate functions, read in a frame
along the whole homotopy, reparametrization or disc. These are the integers that a framing section
of a line bundle on a closed four-manifold assigns to discs, the input of the reconstruction of
pseudoholomorphic curves from positive cohomology assignments.

## Main definitions

* `ContinuousMap.sectionZeroCharge α σ`: the zero charge of the disc `σ` for the map `α` to the
  total space of a complex line bundle.

## Main results

* `ContinuousMap.sectionZeroCharge_eq_zeroCharge`: the zero charge in any continuous frame along
  `σ`.
* `ContinuousMap.sectionZeroCharge_eq_zeroCharge_of_mem_baseSet`: the zero charge in a local
  trivialization.
* `ContinuousMap.sectionZeroCharge_eq_of_eq_smul`: invariance under nonvanishing rescaling.
* `ContinuousMap.sectionZeroCharge_eq_of_homotopy`, `ContinuousMap.sectionZeroCharge_comp`,
  `ContinuousMap.sectionZeroCharge_eq_sum`: the homotopy, degree and additivity laws.
* `ContinuousMap.exists_sectionZeroCharge_comp_eq_zeroCharge`: along a map from a contractible
  space, the zero charges are those of the coordinate function in a frame.

## References

* C. H. Taubes, *SW ⇒ Gr: from the Seiberg–Witten equations to pseudo-holomorphic curves*,
  J. Amer. Math. Soc. 9 (1996), 845–918, Section 6.
-/

public section

noncomputable section

open Bundle Metric Set TauCeti
open TauCeti.Complex.UnitDisc
open scoped Complex.UnitDisc

namespace ContinuousMap

variable {Y : Type*} [TopologicalSpace Y]
  {E : Y → Type*} [∀ y, AddCommGroup (E y)] [∀ y, Module ℂ (E y)] [∀ y, TopologicalSpace (E y)]
  [TopologicalSpace (TotalSpace ℂ E)] [FiberBundle ℂ E] [VectorBundle ℂ ℂ E]
  [∀ y, IsTopologicalAddGroup (E y)] [∀ y, ContinuousSMul ℂ (E y)]
  (α : C(Y, TotalSpace ℂ E))

/-- The **zero charge** of a disc `σ : 𝔻 → Y` for a continuous map `α` to the total space of a
complex line bundle `E`, for instance a section: the zero charge (`ContinuousMap.zeroCharge`) of
the coordinate function of `α ∘ σ` in a continuous frame of `E` along `σ`. It counts the zeros of
`α ∘ σ` with their topological multiplicities, does not depend on the frame
(`ContinuousMap.sectionZeroCharge_eq_zeroCharge`), and is `0` when the zero set of `α ∘ σ` is not
compact. -/
def sectionZeroCharge (σ : C(𝔻, Y)) : ℤ :=
  (ContinuousMap.id ℂ).zeroCharge
    (exists_continuous_frame_coordinate (𝕜 := ℂ) (α.comp σ)).choose_spec.choose

/-- **The zero charge in a frame.** If `φ` is a continuous frame of `E` along a map `g` and `c` is
the coordinate function of `α ∘ σ` in it, then the zero charge of `σ` for `α` is the zero charge of
the disc `c` in `ℂ`. -/
theorem sectionZeroCharge_eq_zeroCharge {σ : C(𝔻, Y)} {g : 𝔻 → Y} {φ : ∀ z, ℂ ≃L[ℂ] E (g z)}
    (hφ : Continuous fun q : 𝔻 × ℂ ↦ TotalSpace.mk' ℂ (g q.1) (φ q.1 q.2)) {c : C(𝔻, ℂ)}
    (hc : ∀ z, TotalSpace.mk' ℂ (g z) (φ z (c z)) = α (σ z)) :
    α.sectionZeroCharge σ = (ContinuousMap.id ℂ).zeroCharge c := by
  have hspec := (exists_continuous_frame_coordinate (𝕜 := ℂ) (α.comp σ)).choose_spec
  set ψ := (exists_continuous_frame_coordinate (𝕜 := ℂ) (α.comp σ)).choose
  set c' := hspec.choose
  obtain ⟨hψ, hc'⟩ := hspec.choose_spec
  -- The two frames differ by a continuous family `A` of automorphisms of `ℂ`.
  obtain ⟨A, hA, hAφ⟩ := exists_continuous_transition_of_continuous_frame (𝕜 := ℂ)
    (g := fun z ↦ ((α.comp σ) z).proj) (fun z ↦ congrArg TotalSpace.proj (hc z)) hφ hψ
  -- `A` is multiplication by the nonvanishing function `a`, which turns `c` into `c'`.
  let a : C(𝔻, ℂ) := ⟨fun z ↦ A z 1, hA.clm_apply continuous_const⟩
  have ha (z : 𝔻) : a z ≠ 0 := (A z).map_ne_zero_iff.2 one_ne_zero
  have hac : c' = a * c := by
    ext z
    have h := (hc' z).trans ((hc z).symm.trans (hAφ z (c z)).symm)
    have ha1 : a z = A z 1 := rfl
    have h2 : A z (c z) = c z * A z 1 := by
      simpa using (A z).map_smul (c z) 1
    rw [(ψ z).injective (TotalSpace.mk_inj.1 h), ContinuousMap.mul_apply, h2, ha1, mul_comm]
  -- By definition, the zero charge is computed in the chosen frame `ψ`.
  have hdef : α.sectionZeroCharge σ = (ContinuousMap.id ℂ).zeroCharge c' := rfl
  rw [hdef, hac]
  exact id_zeroCharge_mul_left c ha

omit [FiberBundle ℂ E] [VectorBundle ℂ ℂ E] [∀ y, IsTopologicalAddGroup (E y)]
  [∀ y, ContinuousSMul ℂ (E y)] in
/-- The value of `α ∘ G` is the frame applied to its coordinate. -/
private theorem snd_eq_frame_apply {B : Type*} {G : B → Y} {Φ : ∀ b, ℂ ≃L[ℂ] E (α (G b)).proj}
    {C : B → ℂ} (hC : ∀ b, TotalSpace.mk' ℂ (α (G b)).proj (Φ b (C b)) = α (G b)) (b : B) :
    (α (G b)).snd = Φ b (C b) :=
  (TotalSpace.mk_inj.1 ((hC b).trans (TotalSpace.eta _).symm)).symm

/-- A frame along `α ∘ G` and the coordinate in it, read along a map `j : 𝔻 → B` with
`G ∘ j = σ`, compute the zero charge of `σ`. -/
private theorem sectionZeroCharge_eq_comp {B : Type*} [TopologicalSpace B] {G : C(B, Y)}
    {Φ : ∀ b, ℂ ≃L[ℂ] E (α (G b)).proj}
    (hΦ : Continuous fun q : B × ℂ ↦ TotalSpace.mk' ℂ (α (G q.1)).proj (Φ q.1 q.2))
    {C : C(B, ℂ)} (hC : ∀ b, TotalSpace.mk' ℂ (α (G b)).proj (Φ b (C b)) = α (G b))
    {σ : C(𝔻, Y)} (j : C(𝔻, B)) (hσ : ∀ z, G (j z) = σ z) :
    α.sectionZeroCharge σ = (ContinuousMap.id ℂ).zeroCharge (C.comp j) :=
  α.sectionZeroCharge_eq_zeroCharge (g := fun z ↦ (α (G (j z))).proj) (φ := fun z ↦ Φ (j z))
    (hΦ.comp (j.continuous.prodMap continuous_id)) fun z ↦ (hC (j z)).trans (by rw [hσ])

omit [FiberBundle ℂ E] [VectorBundle ℂ ℂ E] [∀ y, IsTopologicalAddGroup (E y)]
  [∀ y, ContinuousSMul ℂ (E y)] in
/-- The coordinate of `α ∘ G` vanishes exactly at the zeros of `α ∘ G`. -/
private theorem preimage_coordinate_zero {B : Type*} {G : B → Y}
    {Φ : ∀ b, ℂ ≃L[ℂ] E (α (G b)).proj} {C : B → ℂ}
    (hC : ∀ b, TotalSpace.mk' ℂ (α (G b)).proj (Φ b (C b)) = α (G b)) :
    C ⁻¹' ((ContinuousMap.id ℂ) ⁻¹' {0}) = G ⁻¹' {y | (α y).snd = 0} := by
  ext b
  simp [snd_eq_frame_apply α hC b]

/-- The zero charge vanishes when the zero set of `α ∘ σ` is not compact. -/
@[simp]
theorem sectionZeroCharge_of_not_isCompact {σ : C(𝔻, Y)}
    (h : ¬IsCompact {z | (α (σ z)).snd = 0}) : α.sectionZeroCharge σ = 0 := by
  obtain ⟨Φ, C, hΦ, hC⟩ := exists_continuous_frame_coordinate (𝕜 := ℂ) (α.comp σ)
  rw [α.sectionZeroCharge_eq_comp hΦ hC (ContinuousMap.id 𝔻) fun _ ↦ rfl, C.comp_id]
  exact zeroCharge_of_not_isCompact ((preimage_coordinate_zero α hC).symm ▸ h)

/-- **Vacuum.** The zero charge of a disc missing the zeros of `α` vanishes. -/
theorem sectionZeroCharge_eq_zero_of_forall_ne_zero {σ : C(𝔻, Y)}
    (h : ∀ z, (α (σ z)).snd ≠ 0) : α.sectionZeroCharge σ = 0 := by
  obtain ⟨Φ, C, hΦ, hC⟩ := exists_continuous_frame_coordinate (𝕜 := ℂ) (α.comp σ)
  rw [α.sectionZeroCharge_eq_comp hΦ hC (ContinuousMap.id 𝔻) fun _ ↦ rfl, C.comp_id]
  refine zeroCharge_eq_zero_of_forall_ne_zero fun z hz ↦ h z ?_
  rw [snd_eq_frame_apply α hC z, (Φ z).map_eq_zero_iff]
  exact hz

/-- **The zero charge in a local trivialization.** If `σ` lands in the base set of a linear
trivialization `e` of `E` and `c` is the coordinate function `z ↦ (e (α (σ z))).2` of `α ∘ σ` in
`e`, the zero charge of `σ` for `α` is the zero charge of the disc `c` in `ℂ`. -/
theorem sectionZeroCharge_eq_zeroCharge_of_mem_baseSet (e : Trivialization ℂ (π ℂ E)) [e.IsLinear ℂ]
    {σ : C(𝔻, Y)} (he : ∀ z, (α (σ z)).proj ∈ e.baseSet) {c : C(𝔻, ℂ)}
    (hc : ∀ z, (e (α (σ z))).2 = c z) :
    α.sectionZeroCharge σ = (ContinuousMap.id ℂ).zeroCharge c := by
  let g : 𝔻 → Y := fun z ↦ (α (σ z)).proj
  have hg : Continuous g := (FiberBundle.continuous_proj ℂ E).comp (α.comp σ).continuous
  refine α.sectionZeroCharge_eq_zeroCharge (g := g)
    (φ := fun z ↦ (e.continuousLinearEquivAt ℂ _ (he z)).symm) ?_ fun z ↦ ?_
  · refine (e.continuousOn_symm.comp_continuous (hg.prodMap continuous_id)
      fun q ↦ ⟨he q.1, mem_univ _⟩).congr fun q ↦ ?_
    simp [e.symm_continuousLinearEquivAt_eq (R := ℂ) (he q.1), e.symmL_apply (R := ℂ) (he q.1), g]
  · rw [← hc z]
    simp [e.symm_continuousLinearEquivAt_eq (R := ℂ) (he z), e.symmL_apply (R := ℂ) (he z),
      e.symm_proj_apply _ (he z), g]

/-- **Gauge invariance.** If, along `σ`, `β` is `α` multiplied by a continuous function `u` on the
disc that vanishes nowhere, then `β` and `α` give `σ` the same zero charge. -/
theorem sectionZeroCharge_eq_of_eq_smul {β : C(Y, TotalSpace ℂ E)} {σ : C(𝔻, Y)} {u : C(𝔻, ℂ)}
    (hβ : ∀ z, β (σ z) = TotalSpace.mk' ℂ (α (σ z)).proj (u z • (α (σ z)).snd))
    (hu : ∀ z, u z ≠ 0) :
    β.sectionZeroCharge σ = α.sectionZeroCharge σ := by
  obtain ⟨Φ, C, hΦ, hC⟩ := exists_continuous_frame_coordinate (𝕜 := ℂ) (α.comp σ)
  -- In the frame `Φ`, the coordinate of `β ∘ σ` is `u * C`.
  have hβC (z : 𝔻) :
      TotalSpace.mk' ℂ (α (σ z)).proj (Φ z ((u * C) z)) = β (σ z) := by
    rw [hβ, snd_eq_frame_apply α hC z]
    simp [← smul_eq_mul, map_smul]
  rw [α.sectionZeroCharge_eq_comp hΦ hC (ContinuousMap.id 𝔻) fun _ ↦ rfl, C.comp_id,
    β.sectionZeroCharge_eq_zeroCharge hΦ hβC]
  exact id_zeroCharge_mul_left C hu

/-- **Homotopy invariance.** The zero charge is constant along a homotopy of discs whose total
preimage of the zeros of `α` in `[0, 1] × 𝔻` is compact. -/
theorem sectionZeroCharge_eq_of_homotopy {σ₀ σ₁ : C(𝔻, Y)} (F : σ₀.Homotopy σ₁)
    (hF : IsCompact ((F : unitInterval × 𝔻 → Y) ⁻¹' {y | (α y).snd = 0})) :
    α.sectionZeroCharge σ₀ = α.sectionZeroCharge σ₁ := by
  -- A frame along the whole homotopy, over the contractible paracompact `[0, 1] × 𝔻`.
  obtain ⟨Φ, C, hΦ, hC⟩ :=
    exists_continuous_frame_coordinate (𝕜 := ℂ) (α.comp (F : C(unitInterval × 𝔻, Y)))
  -- The coordinate `C` is a homotopy between the coordinates of the two ends.
  let j (t : unitInterval) : C(𝔻, unitInterval × 𝔻) := ⟨fun z ↦ (t, z), by fun_prop⟩
  rw [α.sectionZeroCharge_eq_comp hΦ hC (j 0) F.apply_zero,
    α.sectionZeroCharge_eq_comp hΦ hC (j 1) F.apply_one]
  let H : (C.comp (j 0)).Homotopy (C.comp (j 1)) :=
    { toContinuousMap := C
      map_zero_left := fun _ ↦ rfl
      map_one_left := fun _ ↦ rfl }
  exact zeroCharge_eq_of_homotopy _ H ((preimage_coordinate_zero α hC).symm ▸ hF)

/-- **The degree law.** For a proper reparametrization `θ : 𝔻 → 𝔻` of a disc `σ` with compact
preimage of the zeros of `α`, the zero charge of `σ ∘ θ` is `deg θ` times that of `σ`, the degree
being taken for any orientation `o` of `𝔻` on both sides. -/
theorem sectionZeroCharge_comp (o : HomologicalOrientation 𝔻 ℂ 2) {σ : C(𝔻, Y)}
    (h : IsCompact (σ ⁻¹' {y | (α y).snd = 0})) {θ : C(𝔻, 𝔻)} (hθ : IsProperMap θ) :
    α.sectionZeroCharge (σ.comp θ) =
      o.degree o Complex.finrank_real_complex θ * α.sectionZeroCharge σ := by
  obtain ⟨Φ, C, hΦ, hC⟩ := exists_continuous_frame_coordinate (𝕜 := ℂ) (α.comp σ)
  rw [α.sectionZeroCharge_eq_comp hΦ hC θ fun _ ↦ rfl,
    α.sectionZeroCharge_eq_comp hΦ hC (ContinuousMap.id 𝔻) fun _ ↦ rfl, C.comp_id]
  exact zeroCharge_comp o ((preimage_coordinate_zero α hC).symm ▸ h) hθ

/-- **Additivity.** If finitely many disjoint round subdiscs `B(cᵢ, rᵢ) ⊆ 𝔻` contain every zero
of `α ∘ σ`, and the zeros of `α ∘ σ` form a compact set, the zero charge of `σ` is the sum of the
zero charges of the restrictions of `σ` to these subdiscs. -/
theorem sectionZeroCharge_eq_sum {ι : Type} [Fintype ι] {σ : C(𝔻, Y)}
    (h : IsCompact (σ ⁻¹' {y | (α y).snd = 0})) (c : ι → ℂ) (r : ι → ℝ)
    (hc : ∀ i, ‖c i‖ + r i ≤ 1) (hr : ∀ i, 0 < r i)
    (hdisj : Pairwise fun i j ↦ Disjoint (ball (c i) (r i)) (ball (c j) (r j)))
    (hcov : ∀ z, (α (σ z)).snd = 0 → ∃ i, (z : ℂ) ∈ ball (c i) (r i)) :
    α.sectionZeroCharge σ =
      ∑ i, α.sectionZeroCharge (σ.comp (subdisc (c i) (r i) (hc i) (hr i))) := by
  obtain ⟨Φ, C, hΦ, hC⟩ := exists_continuous_frame_coordinate (𝕜 := ℂ) (α.comp σ)
  have hZ := preimage_coordinate_zero α hC
  rw [α.sectionZeroCharge_eq_comp hΦ hC (ContinuousMap.id 𝔻) fun _ ↦ rfl, C.comp_id,
    zeroCharge_eq_sum (hZ.symm ▸ h) c r hc hr hdisj fun z hz ↦ hcov z ?_]
  · exact Finset.sum_congr rfl fun i _ ↦
      (α.sectionZeroCharge_eq_comp hΦ hC (subdisc (c i) (r i) (hc i) (hr i)) fun _ ↦ rfl).symm
  · exact (Set.ext_iff.1 hZ z).1 hz

/-- **The zero charges along a map are those of a function.** Along a continuous map `G : B → Y`
from a contractible paracompact R₁ space, for instance the disc `𝔻` or the cylinder
`[0, 1] × 𝔻`, the zero charges of the discs `G ∘ τ` for `α` are the zero charges of the discs `τ`
for one continuous function `c : B → ℂ`, which vanishes exactly where `α ∘ G` does: the coordinate
of `α ∘ G` in a continuous frame of `E` along it. -/
theorem exists_sectionZeroCharge_comp_eq_zeroCharge {B : Type*} [TopologicalSpace B] [R1Space B]
    [ParacompactSpace B] [ContractibleSpace B] (G : C(B, Y)) :
    ∃ c : C(B, ℂ), (∀ τ : C(𝔻, B), α.sectionZeroCharge (G.comp τ) = c.zeroCharge τ) ∧
      ∀ b, c b = 0 ↔ (α (G b)).snd = 0 := by
  obtain ⟨Φ, C, hΦ, hC⟩ := exists_continuous_frame_coordinate (𝕜 := ℂ) (α.comp G)
  refine ⟨C, fun τ ↦ ?_, fun b ↦ ?_⟩
  · rw [α.sectionZeroCharge_eq_comp hΦ hC τ fun _ ↦ rfl, id_zeroCharge_comp]
  · rw [snd_eq_frame_apply α hC b, (Φ b).map_eq_zero_iff]

end ContinuousMap
