/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.DirectSum.Internal
public import TauCeti.Algebra.Homology.DG.Module.Right.QuasiIso

/-!
# The canonical truncation of a DG right module

Let `(𝒜, d)` be a differential graded algebra concentrated in nonpositive cohomological degrees,
`𝒜 n = 0` for `n > 0`, such as the chains `C_*(Ω_b B)` on the Moore loops of a space read
cohomologically through `C^{-n} = C_n`. For a DG right module `M` over it and an integer `m`, the
**canonical truncation** `τ^{≤ m} M` (`TauCeti.DGRightModuleCat.truncLE`) consists of the
elements of `M` whose homogeneous components vanish above degree `m` and whose degree-`m`
component is a cycle: it is `M^p` in degrees `p < m`, the cycles `Z^m(M)` in degree `m` and `0`
above. In the homological grading of chains it is the truncation `τ_{≥ k}` with `k = -m`, which
keeps the chains of degree `> k` and the cycles of degree `k`.

As a cochain complex this is the canonical truncation of complexes (Mathlib's
`CochainComplex.truncLE` is the corresponding construction in an abelian category). The point of
this file is that, over a nonpositively graded algebra, it is a **sub-DG module**: acting by an
element of negative degree lowers degrees, and an element `a` of degree `0` has `d a = 0` for
degree reasons, so by the Leibniz rule it sends a cycle of degree `m` to a cycle of degree `m`
(`TauCeti.DGRightModuleCat.truncLESubmodule` is a right submodule). Its inclusion
`TauCeti.DGRightModuleCat.ιTruncLE` is a morphism of DG right modules, and

* it is injective on cohomology (`TauCeti.DGRightModuleCat.injective_cohomologyMap_ιTruncLE`),
  and every class of `M` of degree `p ≤ m` is the image of a class of `τ^{≤ m} M` of degree `p`
  (`TauCeti.DGRightModuleCat.exists_cohomologyMap_ιTruncLE_eq`), so it induces
  `H^p(τ^{≤ m} M) ≅ H^p(M)` for `p ≤ m`;
* the cohomology of `τ^{≤ m} M` vanishes in degrees `p > m`
  (`TauCeti.DGRightModuleCat.cohomologyGrading_truncLE_eq_bot`);
* when the cohomology of `M` vanishes above `m` the inclusion is a quasi-isomorphism
  (`TauCeti.DGRightModuleCat.isQuasiIso_ιTruncLE`).

The truncations increase with `m` (`TauCeti.DGRightModuleCat.truncLESubmodule_mono`, with the
morphisms `TauCeti.DGRightModuleCat.truncLEInclusion` between them) and exhaust `M`
(`TauCeti.DGRightModuleCat.iSup_truncLESubmodule`), every finite set of elements lying in one of
them (`TauCeti.DGRightModuleCat.exists_forall_mem_truncLESubmodule`): every DG module over such an
algebra is the directed union of sub-DG modules whose cohomology is bounded above, that is,
homologically bounded below. This reduces statements about DG local systems with cohomology
bounded on one side, proved through convergent spectral sequences, to arbitrary DG local systems,
by passing to the directed colimit (`TauCeti.Algebra.Homology.DG.Twisted.RowFinite.DirectedUnion`
does this for twisted complexes).

The hypothesis on `𝒜` cannot be dropped: over the graded algebra `R[t]` with `t` of degree `1`
and zero differential, acting freely on itself, the cycle `1` of degree `0` lies in `τ^{≤ 0}`
while `1 · t = t` has degree `1`. For the chains on Moore loops the hypothesis is
`TauCeti.cubicalChainGrading_eq_bot`.

## Main definitions

* `TauCeti.DGRightModuleCat.truncLESubmodule`: the elements of `τ^{≤ m} M`, as a right submodule.
* `TauCeti.DGRightModuleCat.truncLE`: the canonical truncation `τ^{≤ m} M` as a DG right module.
* `TauCeti.DGRightModuleCat.ιTruncLE`: its inclusion into `M`.
* `TauCeti.DGRightModuleCat.truncLEInclusion`: the inclusion `τ^{≤ m} M ⟶ τ^{≤ m'} M` for `m ≤ m'`.

## References

* C. A. Weibel, *An Introduction to Homological Algebra*, Cambridge Studies in Advanced
  Mathematics 38, Cambridge University Press, 1994, §1.2 (truncations).
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, Corollary 4.17 and the proof of
  Theorem K.
-/

public section

open CategoryTheory DirectSum MulOpposite

namespace TauCeti

namespace DGRightModuleCat

universe uR uA uM

variable {R : Type uR} {A : Type uA} [CommRing R] [Ring A] [Algebra R A]
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {d : A →ₗ[R] A} {h : IsDGAlgebra 𝒜 d}
  (M : DGRightModuleCat.{uR, uA, uM} h)

/-! ### The underlying submodule -/

section Carrier

/-- The elements of the canonical truncation `τ^{≤ m} M` as an `R`-submodule: those whose
components of degree above `m` vanish and whose component of degree `m` is a cycle. -/
private def truncLECarrier (m : ℤ) : Submodule R M where
  carrier := {x | (∀ p, m < p → (decompose M.grading x p : M) = 0) ∧
    M.differential (decompose M.grading x m : M) = 0}
  add_mem' {x y} hx hy := by
    refine ⟨fun p hp ↦ ?_, ?_⟩
    · simp [decompose_add, hx.1 p hp, hy.1 p hp]
    · simp [decompose_add, hx.2, hy.2]
  zero_mem' := by simp
  smul_mem' r x hx := by
    refine ⟨fun p hp ↦ ?_, ?_⟩
    · rw [decompose_smul, DirectSum.smul_apply, Submodule.coe_smul, hx.1 p hp, smul_zero]
    · rw [decompose_smul, DirectSum.smul_apply, Submodule.coe_smul, map_smul, hx.2, smul_zero]

variable {M}

/-- A homogeneous element of degree `p` lies in `τ^{≤ m}` exactly when it vanishes if `p > m` and
is a cycle if `p = m`. -/
private theorem mem_truncLECarrier_iff_of_mem {m p : ℤ} {y : M} (hy : y ∈ M.grading p) :
    y ∈ truncLECarrier M m ↔ (m < p → y = 0) ∧ (p = m → M.differential y = 0) := by
  classical
  constructor
  · rintro ⟨h₁, h₂⟩
    refine ⟨fun hp ↦ ?_, ?_⟩
    · simpa [decompose_of_mem_same M.grading hy] using h₁ p hp
    · rintro rfl
      simpa [decompose_of_mem_same M.grading hy] using h₂
  · rintro ⟨h₁, h₂⟩
    refine ⟨fun q hq ↦ ?_, ?_⟩
    · by_cases hqp : p = q
      · subst hqp
        simp [h₁ hq]
      · exact decompose_of_mem_ne M.grading hy hqp
    · by_cases hpm : p = m
      · subst hpm
        simpa [decompose_of_mem_same M.grading hy] using h₂ rfl
      · simp [decompose_of_mem_ne M.grading hy hpm]

/-- The homogeneous components of an element of `τ^{≤ m}` lie in `τ^{≤ m}`. -/
private theorem decompose_mem_truncLECarrier {m : ℤ} {x : M} (hx : x ∈ truncLECarrier M m)
    (q : ℤ) : (decompose M.grading x q : M) ∈ truncLECarrier M m := by
  rw [mem_truncLECarrier_iff_of_mem (SetLike.coe_mem _)]
  exact ⟨hx.1 q, fun hq ↦ hq ▸ hx.2⟩

/-- The truncation is stable under the differential. -/
private theorem differential_mem_truncLECarrier {m : ℤ} {x : M} (hx : x ∈ truncLECarrier M m) :
    M.differential x ∈ truncLECarrier M m := by
  classical
  rw [← sum_support_decompose M.grading x, map_sum]
  refine Submodule.sum_mem _ fun q _ ↦ ?_
  have hq := decompose_mem_truncLECarrier hx q
  rw [mem_truncLECarrier_iff_of_mem (SetLike.coe_mem _)] at hq
  rw [mem_truncLECarrier_iff_of_mem
    (M.isDGRightModule.isHomogeneous.map_mem (SetLike.coe_mem (decompose M.grading x q)))]
  refine ⟨fun hmq ↦ ?_, fun _ ↦ M.isDGRightModule.sq_zero _⟩
  rcases lt_or_eq_of_le (Int.le_of_lt_add_one hmq) with hlt | rfl
  · rw [hq.1 hlt, map_zero]
  · exact hq.2 rfl

variable (h𝒜 : ∀ n, 0 < n → 𝒜 n = ⊥)
include h𝒜

/-- A homogeneous algebra element acting on a homogeneous element of `τ^{≤ m}` gives an element
of `τ^{≤ m}`. -/
private theorem op_smul_mem_truncLECarrier_of_mem {m e p : ℤ} {a : A} (ha : a ∈ 𝒜 e) {y : M}
    (hy : y ∈ M.grading p) (hyτ : y ∈ truncLECarrier M m) :
    op a • y ∈ truncLECarrier M m := by
  rcases lt_or_ge 0 e with he | he
  · rw [h𝒜 e he, Submodule.mem_bot] at ha
    rw [ha, op_zero, zero_smul]
    exact zero_mem _
  rw [mem_truncLECarrier_iff_of_mem hy] at hyτ
  rw [mem_truncLECarrier_iff_of_mem (op_smul_mem_of_mem_graded ha hy)]
  rcases lt_trichotomy p m with hpm | rfl | hpm
  · exact ⟨fun h ↦ absurd h (by omega), fun h ↦ absurd h (by omega)⟩
  · rcases lt_or_eq_of_le he with he | rfl
    · exact ⟨fun h ↦ absurd h (by omega), fun h ↦ absurd h (by omega)⟩
    · refine ⟨fun h ↦ absurd h (by omega), fun _ ↦ ?_⟩
      have hda : d a = 0 := by
        have := h.map_mem ha
        rwa [zero_add, h𝒜 1 one_pos, Submodule.mem_bot] at this
      rw [M.isDGRightModule.leibniz_of_map_eq_zero y hda, hyτ.2 rfl, smul_zero]
  · rw [hyτ.1 hpm, smul_zero]
    exact ⟨fun _ ↦ rfl, fun _ ↦ map_zero _⟩

/-- The truncation is stable under the right action of the algebra. -/
private theorem op_smul_mem_truncLECarrier {m : ℤ} (a : A) {x : M}
    (hx : x ∈ truncLECarrier M m) : op a • x ∈ truncLECarrier M m := by
  classical
  rw [← sum_support_decompose 𝒜 a, ← sum_support_decompose M.grading x, Finset.op_sum,
    Finset.sum_smul]
  refine Submodule.sum_mem _ fun e _ ↦ ?_
  rw [Finset.smul_sum]
  refine Submodule.sum_mem _ fun q _ ↦ ?_
  exact op_smul_mem_truncLECarrier_of_mem h𝒜 (SetLike.coe_mem _) (SetLike.coe_mem _)
    (decompose_mem_truncLECarrier hx q)

end Carrier

/-- The elements of the canonical truncation `τ^{≤ m} M` of a DG right module over a
nonpositively graded DG algebra, as a right submodule: those whose components of degree above `m`
vanish and whose component of degree `m` is a cycle. -/
def truncLESubmodule (h𝒜 : ∀ n, 0 < n → 𝒜 n = ⊥) (m : ℤ) : Submodule Aᵐᵒᵖ M :=
  { (truncLECarrier M m).toAddSubmonoid with
    smul_mem' := fun a _ hx ↦ by
      have := op_smul_mem_truncLECarrier h𝒜 a.unop hx
      rw [op_unop] at this
      exact this }

variable {M} {h𝒜 : ∀ n, 0 < n → 𝒜 n = ⊥}

/-- Membership in `τ^{≤ m} M`: the components of degree above `m` vanish and the component of
degree `m` is a cycle. -/
theorem mem_truncLESubmodule {m : ℤ} {x : M} :
    x ∈ M.truncLESubmodule h𝒜 m ↔ (∀ p, m < p → (decompose M.grading x p : M) = 0) ∧
      M.differential (decompose M.grading x m : M) = 0 :=
  Iff.rfl

/-- A homogeneous element of degree `p` lies in `τ^{≤ m} M` exactly when it vanishes if `m < p`
and is a cycle if `p = m`. -/
theorem mem_truncLESubmodule_iff_of_mem {m p : ℤ} {y : M} (hy : y ∈ M.grading p) :
    y ∈ M.truncLESubmodule h𝒜 m ↔ (m < p → y = 0) ∧ (p = m → M.differential y = 0) :=
  mem_truncLECarrier_iff_of_mem hy

/-- Every homogeneous element of degree `p < m` lies in `τ^{≤ m} M`. -/
theorem mem_truncLESubmodule_of_lt {m p : ℤ} {y : M} (hy : y ∈ M.grading p) (hpm : p < m) :
    y ∈ M.truncLESubmodule h𝒜 m :=
  (mem_truncLESubmodule_iff_of_mem hy).2
    ⟨fun h ↦ absurd h (by omega), fun h ↦ absurd h (by omega)⟩

/-- Every cycle of degree `m` lies in `τ^{≤ m} M`. -/
theorem mem_truncLESubmodule_of_differential_eq_zero {m : ℤ} {y : M} (hy : y ∈ M.grading m)
    (hdy : M.differential y = 0) : y ∈ M.truncLESubmodule h𝒜 m :=
  (mem_truncLESubmodule_iff_of_mem hy).2 ⟨fun h ↦ absurd h (lt_irrefl m), fun _ ↦ hdy⟩

variable (M h𝒜) in
/-- `τ^{≤ m} M` is homogeneous: the homogeneous components of its elements lie in it. -/
theorem isHomogeneous_truncLESubmodule (m : ℤ) :
    (M.truncLESubmodule h𝒜 m).IsHomogeneous M.grading :=
  fun q _ hx ↦ decompose_mem_truncLECarrier hx q

/-- The differential of an element of `τ^{≤ m} M` lies in `τ^{≤ m} M`. -/
theorem differential_mem_truncLESubmodule {m : ℤ} {x : M} (hx : x ∈ M.truncLESubmodule h𝒜 m) :
    M.differential x ∈ M.truncLESubmodule h𝒜 m :=
  differential_mem_truncLECarrier hx

/-- The truncations increase with the truncation degree. -/
theorem truncLESubmodule_mono : Monotone (M.truncLESubmodule h𝒜) := by
  intro m m' hmm' x hx
  rw [mem_truncLESubmodule] at hx ⊢
  refine ⟨fun p hp ↦ hx.1 p (lt_of_le_of_lt hmm' hp), ?_⟩
  rcases lt_or_eq_of_le hmm' with hlt | rfl
  · rw [hx.1 m' hlt, map_zero]
  · exact hx.2

/-- Every element of `M` lies in some truncation `τ^{≤ m} M`. -/
theorem exists_mem_truncLESubmodule (x : M) : ∃ m, x ∈ M.truncLESubmodule h𝒜 m := by
  classical
  obtain ⟨b, hb⟩ := (decompose M.grading x).support.bddAbove
  have hzero : ∀ p, b < p → (decompose M.grading x p : M) = 0 := fun p hp ↦ by
    have hp' : p ∉ (decompose M.grading x).support := fun hmem ↦ absurd (hb hmem) (not_le.2 hp)
    rw [DFinsupp.notMem_support_iff.1 hp', ZeroMemClass.coe_zero]
  exact ⟨b + 1, mem_truncLESubmodule.2
    ⟨fun p hp ↦ hzero p (by omega), by rw [hzero (b + 1) (by omega), map_zero]⟩⟩

/-- Every finite set of elements of `M` lies in one truncation `τ^{≤ m} M`: the truncations form a
directed family exhausting `M`. -/
theorem exists_forall_mem_truncLESubmodule (s : Finset M) :
    ∃ m, ∀ x ∈ s, x ∈ M.truncLESubmodule h𝒜 m := by
  classical
  choose k hk using fun x : M ↦ exists_mem_truncLESubmodule (h𝒜 := h𝒜) x
  obtain ⟨b, hb⟩ := (s.image k).bddAbove
  exact ⟨b, fun x hx ↦ truncLESubmodule_mono (hb (Finset.mem_image_of_mem k hx)) (hk x)⟩

/-- **The truncations exhaust the module.** -/
theorem iSup_truncLESubmodule : ⨆ m, M.truncLESubmodule h𝒜 m = ⊤ :=
  eq_top_iff.2 fun x _ ↦ by
    obtain ⟨m, hm⟩ := exists_mem_truncLESubmodule (h𝒜 := h𝒜) x
    exact Submodule.mem_iSup_of_mem m hm

/-! ### The truncation as a DG right module -/

variable (M h𝒜)

/-- The grading of `τ^{≤ m} M`, inherited from `M`. -/
private def truncLEGrading (m : ℤ) (p : ℤ) : Submodule R (M.truncLESubmodule h𝒜 m) :=
  (M.grading p).comap ((M.truncLESubmodule h𝒜 m).subtype.restrictScalars R)

/-- The differential of `τ^{≤ m} M`, the restriction of the differential of `M`. -/
private def truncLEDifferential (m : ℤ) :
    M.truncLESubmodule h𝒜 m →ₗ[R] M.truncLESubmodule h𝒜 m :=
  (M.differential.comp ((M.truncLESubmodule h𝒜 m).subtype.restrictScalars R)).codRestrict
    ((M.truncLESubmodule h𝒜 m).restrictScalars R) fun x ↦
      differential_mem_truncLESubmodule x.property

private noncomputable instance (m : ℤ) : Decomposition (truncLEGrading M h𝒜 m) :=
  TauCeti.DirectSum.Decomposition.restrict M.grading (truncLEGrading M h𝒜 m)
    ((M.truncLESubmodule h𝒜 m).subtype.restrictScalars R) Subtype.val_injective
    (fun _ _ ↦ Iff.rfl) fun p x ↦
      ⟨⟨(decompose M.grading (x : M) p : M),
        M.isHomogeneous_truncLESubmodule h𝒜 m p x.property⟩, rfl⟩

private instance (m : ℤ) :
    SetLike.GradedSMul (InternalGrading.ofDecomposition 𝒜).opposite.piece
      (truncLEGrading M h𝒜 m) where
  smul_mem {_ _ _ _} ha hx := M.gradedSMul.smul_mem ha hx

/-- **The canonical truncation** `τ^{≤ m} M` of a DG right module over a nonpositively graded DG
algebra: the sub-DG module which is `M^p` in degrees `p < m`, the cycles of `M` in degree `m`, and
`0` above. Its elements are those of `truncLESubmodule` through `truncLEEquiv`. -/
noncomputable def truncLE (m : ℤ) : DGRightModuleCat.{uR, uA, uM} h where
  carrier := M.truncLESubmodule h𝒜 m
  grading := truncLEGrading M h𝒜 m
  differential := truncLEDifferential M h𝒜 m
  isDGRightModule :=
    { isHomogeneous := LinearMap.isHomogeneous_def.2 fun _ _ hx ↦
        M.isDGRightModule.isHomogeneous.map_mem hx
      sq_zero := fun x ↦ Subtype.ext (M.isDGRightModule.sq_zero x)
      leibniz := fun hx a ↦ Subtype.ext (M.isDGRightModule.leibniz hx a) }

/-- The elements of `τ^{≤ m} M` are the elements of `truncLESubmodule`. Consumers use this
equivalence rather than unfolding `truncLE`. -/
noncomputable def truncLEEquiv (m : ℤ) : M.truncLE h𝒜 m ≃ₗ[Aᵐᵒᵖ] M.truncLESubmodule h𝒜 m :=
  LinearEquiv.refl Aᵐᵒᵖ (M.truncLESubmodule h𝒜 m)

variable {M h𝒜}

/-- An element of `τ^{≤ m} M` has degree `p` exactly when it has degree `p` in `M`. -/
@[simp]
theorem mem_truncLE_grading {m p : ℤ} {x : M.truncLE h𝒜 m} :
    x ∈ (M.truncLE h𝒜 m).grading p ↔ (M.truncLEEquiv h𝒜 m x : M) ∈ M.grading p :=
  Iff.rfl

/-- The differential of `τ^{≤ m} M` is the differential of `M`. -/
@[simp]
theorem coe_truncLEEquiv_differential {m : ℤ} (x : M.truncLE h𝒜 m) :
    (M.truncLEEquiv h𝒜 m ((M.truncLE h𝒜 m).differential x) : M) =
      M.differential (M.truncLEEquiv h𝒜 m x) :=
  (rfl)

variable (M h𝒜)

/-- The inclusion `τ^{≤ m} M ⟶ M` of the canonical truncation. -/
noncomputable def ιTruncLE (m : ℤ) : M.truncLE h𝒜 m ⟶ M where
  toLinearMap := (M.truncLESubmodule h𝒜 m).subtype ∘ₗ (M.truncLEEquiv h𝒜 m).toLinearMap
  map_mem' hx := hx
  map_d' _ := (rfl)

variable {M h𝒜}

/-- The inclusion of the truncation sends an element to itself. -/
@[simp]
theorem ιTruncLE_apply {m : ℤ} (x : M.truncLE h𝒜 m) :
    M.ιTruncLE h𝒜 m x = (M.truncLEEquiv h𝒜 m x : M) :=
  (rfl)

/-- The inclusion of the truncation is injective. -/
theorem ιTruncLE_injective (m : ℤ) : Function.Injective (M.ιTruncLE h𝒜 m) :=
  Subtype.val_injective.comp (M.truncLEEquiv h𝒜 m).injective

/-- The image of the inclusion of `τ^{≤ m} M` is `truncLESubmodule`. -/
@[simp]
theorem range_ιTruncLE (m : ℤ) :
    Set.range (M.ιTruncLE h𝒜 m) = M.truncLESubmodule h𝒜 m := by
  ext x
  refine ⟨?_, fun hx ↦ ⟨(M.truncLEEquiv h𝒜 m).symm ⟨x, hx⟩, by simp⟩⟩
  rintro ⟨y, rfl⟩
  exact (M.truncLEEquiv h𝒜 m y).property

variable (M h𝒜) in
/-- The inclusion `τ^{≤ m} M ⟶ τ^{≤ m'} M` of truncations for `m ≤ m'`. -/
noncomputable def truncLEInclusion {m m' : ℤ} (hmm' : m ≤ m') :
    M.truncLE h𝒜 m ⟶ M.truncLE h𝒜 m' where
  toLinearMap := (M.truncLEEquiv h𝒜 m').symm.toLinearMap ∘ₗ
    Submodule.inclusion (truncLESubmodule_mono hmm') ∘ₗ (M.truncLEEquiv h𝒜 m).toLinearMap
  map_mem' hx := hx
  map_d' _ := (rfl)

/-- The inclusion of truncations sends an element to itself. -/
@[simp]
theorem coe_truncLEEquiv_truncLEInclusion {m m' : ℤ} (hmm' : m ≤ m') (x : M.truncLE h𝒜 m) :
    (M.truncLEEquiv h𝒜 m' (M.truncLEInclusion h𝒜 hmm' x) : M) = M.truncLEEquiv h𝒜 m x :=
  (rfl)

/-- The inclusions of truncations are compatible with the inclusions into `M`. -/
@[reassoc (attr := simp)]
theorem truncLEInclusion_ιTruncLE {m m' : ℤ} (hmm' : m ≤ m') :
    M.truncLEInclusion h𝒜 hmm' ≫ M.ιTruncLE h𝒜 m' = M.ιTruncLE h𝒜 m :=
  hom_ext fun _ ↦ by rw [comp_apply]; rfl

/-- The inclusion of a truncation into itself is the identity. -/
@[simp]
theorem truncLEInclusion_refl (m : ℤ) :
    M.truncLEInclusion h𝒜 (le_refl m) = 𝟙 (M.truncLE h𝒜 m) :=
  hom_ext fun _ ↦ by rw [id_apply]; rfl

/-- The inclusions of truncations compose. -/
@[reassoc (attr := simp)]
theorem truncLEInclusion_comp_truncLEInclusion {m m' m'' : ℤ} (hmm' : m ≤ m')
    (hm'm'' : m' ≤ m'') :
    M.truncLEInclusion h𝒜 hmm' ≫ M.truncLEInclusion h𝒜 hm'm'' =
      M.truncLEInclusion h𝒜 (hmm'.trans hm'm'') :=
  hom_ext fun _ ↦ by rw [comp_apply]; rfl

/-! ### Cohomology of the truncation -/

/-- **The truncation is injective on cohomology.** A cycle of `τ^{≤ m} M` that bounds in `M`
already bounds in `τ^{≤ m} M`: keep the components of degree below `m` of a primitive. -/
theorem injective_cohomologyMap_ιTruncLE (m : ℤ) :
    Function.Injective (DGRightModuleHom.cohomologyMap (M.ιTruncLE h𝒜 m)) := by
  classical
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro c hc
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ c
  rw [DGRightModuleHom.cohomologyMap_mk, IsDGRightModule.quotientMk_eq_zero_iff,
    IsDGRightModule.mem_boundaries, DGRightModuleHom.cyclesMap_apply_coe] at hc
  obtain ⟨y, hy⟩ := hc
  rw [IsDGRightModule.quotientMk_eq_zero_iff, IsDGRightModule.mem_boundaries]
  -- The part of `y` of degree below `m` is a primitive of `z` inside the truncation.
  let y' : M := ∑ q ∈ (decompose M.grading y).support with q < m, (decompose M.grading y q : M)
  have hy'τ : y' ∈ M.truncLESubmodule h𝒜 m :=
    Submodule.sum_mem _ fun q hq ↦
      mem_truncLESubmodule_of_lt (SetLike.coe_mem _) (Finset.mem_filter.1 hq).2
  refine ⟨(M.truncLEEquiv h𝒜 m).symm ⟨y', hy'τ⟩, (M.truncLEEquiv h𝒜 m).injective ?_⟩
  refine Subtype.ext ?_
  have hzτ := (M.truncLEEquiv h𝒜 m (z : M.truncLE h𝒜 m)).property
  rw [ιTruncLE_apply] at hy
  -- The components of `y` of degree `q ≥ m` are cycles, since `d (y_q) = z_{q + 1} = 0`.
  have hcyc : ∀ q, ¬q < m → M.differential (decompose M.grading y q : M) = 0 := fun q hq ↦ by
    rw [M.isDGRightModule.map_decompose, hy]
    exact (mem_truncLESubmodule.1 hzτ).1 (q + 1) (by omega)
  rw [coe_truncLEEquiv_differential, LinearEquiv.apply_symm_apply, ← hy]
  conv_rhs => rw [← sum_support_decompose M.grading y, map_sum,
    ← Finset.sum_filter_add_sum_filter_not _ (· < m)]
  rw [Finset.sum_eq_zero fun q hq ↦ hcyc q (Finset.mem_filter.1 hq).2, add_zero, map_sum]

/-- **In degrees `p ≤ m` the truncation is surjective on cohomology.** Every class of degree
`p ≤ m` of `M` is the image of a class of degree `p` of `τ^{≤ m} M`: its representing cycles lie
in the truncation. Together with `injective_cohomologyMap_ιTruncLE` this gives
`H^p(τ^{≤ m} M) ≅ H^p(M)` for `p ≤ m`. -/
theorem exists_cohomologyMap_ιTruncLE_eq {m p : ℤ} (hp : p ≤ m)
    {x : M.isDGRightModule.Cohomology} (hx : x ∈ M.isDGRightModule.cohomologyGrading p) :
    ∃ y ∈ (M.truncLE h𝒜 m).isDGRightModule.cohomologyGrading p,
      DGRightModuleHom.cohomologyMap (M.ιTruncLE h𝒜 m) y = x := by
  obtain ⟨z, hz, rfl⟩ := M.isDGRightModule.mem_cohomologyGrading.1 hx
  have hdz : M.differential z = 0 := M.isDGRightModule.mem_cycles.1 z.property
  have hzτ : (z : M) ∈ M.truncLESubmodule h𝒜 m := by
    rcases lt_or_eq_of_le hp with hlt | rfl
    · exact mem_truncLESubmodule_of_lt hz hlt
    · exact mem_truncLESubmodule_of_differential_eq_zero hz hdz
  have hw : (M.truncLE h𝒜 m).differential ((M.truncLEEquiv h𝒜 m).symm ⟨z, hzτ⟩) = 0 :=
    (M.truncLEEquiv h𝒜 m).injective <| Subtype.ext <| by
      rw [coe_truncLEEquiv_differential, LinearEquiv.apply_symm_apply, map_zero]
      exact hdz
  let w : (M.truncLE h𝒜 m).isDGRightModule.cycles :=
    ⟨(M.truncLEEquiv h𝒜 m).symm ⟨z, hzτ⟩, (M.truncLE h𝒜 m).isDGRightModule.mem_cycles.2 hw⟩
  refine ⟨Submodule.Quotient.mk w, IsDGRightModule.quotientMk_mem_cohomologyGrading _ ?_, ?_⟩
  · rw [mem_truncLE_grading, LinearEquiv.apply_symm_apply]
    exact hz
  · rw [DGRightModuleHom.cohomologyMap_mk]
    congr 1
    exact Subtype.ext (by rw [DGRightModuleHom.cyclesMap_apply_coe, ιTruncLE_apply,
      LinearEquiv.apply_symm_apply])

/-- **The cohomology of the truncation vanishes above the truncation degree.** -/
theorem cohomologyGrading_truncLE_eq_bot {m p : ℤ} (hp : m < p) :
    (M.truncLE h𝒜 m).isDGRightModule.cohomologyGrading p = ⊥ := by
  refine eq_bot_iff.2 fun x hx ↦ ?_
  obtain ⟨z, hz, rfl⟩ := (M.truncLE h𝒜 m).isDGRightModule.mem_cohomologyGrading.1 hx
  rw [mem_truncLE_grading] at hz
  have hz0 := ((mem_truncLESubmodule_iff_of_mem hz).1
    (M.truncLEEquiv h𝒜 m (z : M.truncLE h𝒜 m)).property).1 hp
  have : z = 0 := Subtype.ext <| (M.truncLEEquiv h𝒜 m).injective (Subtype.ext (by simpa using hz0))
  rw [this, Submodule.Quotient.mk_zero, Submodule.mem_bot]

/-- **The truncation is a quasi-isomorphism when the cohomology of `M` vanishes above the
truncation degree.** -/
theorem isQuasiIso_ιTruncLE {m : ℤ}
    (hM : ∀ p, m < p → M.isDGRightModule.cohomologyGrading p = ⊥) :
    IsQuasiIso (M.ιTruncLE h𝒜 m) := by
  classical
  refine (DGRightModuleHom.isQuasiIso_iff _).2 ⟨injective_cohomologyMap_ιTruncLE m, fun x ↦ ?_⟩
  have hx : x ∈ LinearMap.range (DGRightModuleHom.cohomologyMap (M.ιTruncLE h𝒜 m)) := by
    rw [← sum_support_decompose M.isDGRightModule.cohomologyGrading x]
    refine Submodule.sum_mem _ fun p _ ↦ ?_
    rcases le_or_gt p m with hpm | hpm
    · obtain ⟨y, -, hy⟩ := exists_cohomologyMap_ιTruncLE_eq (h𝒜 := h𝒜) hpm
        (SetLike.coe_mem (decompose M.isDGRightModule.cohomologyGrading x p))
      exact ⟨y, hy⟩
    · have h0 : (decompose M.isDGRightModule.cohomologyGrading x p :
          M.isDGRightModule.Cohomology) = 0 :=
        (Submodule.mem_bot R).1 ((hM p hpm).le (SetLike.coe_mem _))
      rw [h0]
      exact zero_mem _
  exact LinearMap.mem_range.1 hx

end DGRightModuleCat

end TauCeti
