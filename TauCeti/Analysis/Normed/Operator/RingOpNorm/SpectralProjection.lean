/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.Complement
public import TauCeti.Analysis.Normed.Operator.RingOpNorm.Banach
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Idempotent
import TauCeti.Algebra.Ring.SpectralIdempotent

/-!
# Spectral projections in operator-norm endomorphism algebras

Let `R` be a seminormed commutative ring with Tate scalars (`TauCeti.NormedRing.IsTate R`), `M` a
seminormed `R`-module with bounded scalar action, and `u, C : M →L[R] M` continuous endomorphisms.

A **spectral projection** of `u` for `C` of order `h`
(`ContinuousLinearMap.IsSpectralProjection u C h E`) is an idempotent `E`, commuting with `u` and
lying in the operator-norm closure of the polynomials in `u`, such that `C ^ h * E = 0` and `C` is
invertible on the complementary summand `range (1 - E)` with complementary inverse `w` again in the
operator-norm closure of `R[u]`.

This common predicate underlies both Riesz projections at a scalar (`C = 1 - a • u`) and
Riesz–Coleman projections for a polynomial factor (`C = Q*(u)`, `h = 1`). All algebraic,
topological, uniqueness, functoriality, retract-compression, and ring-homomorphism transport
properties depend only on this structure:

* `E` commutes with `C` (`ContinuousLinearMap.IsSpectralProjection.commute_spectral`), splits `M`
  into the topological complements `range E = ker C ^ n` and `ker E = range C ^ n` for every
  `n ≥ h` (`ContinuousLinearMap.IsSpectralProjection.isTopCompl_ker_range_pow`), and induces a
  continuous linear automorphism of `ker E` (`ContinuousLinearMap.IsSpectralProjection.equivKer`).
* Spectral projections for the same `C` are unique, even across different `u` and nilpotence bounds
  (`ContinuousLinearMap.IsSpectralProjection.unique`).
* Any linear map intertwining `C` and `D` intertwines their spectral projections and complementary
  inverses (`ContinuousLinearMap.IsSpectralProjection.semiconj`,
  `ContinuousLinearMap.IsSpectralProjection.semiconj_inverse`).
* Spectral projections compress along continuous linear retracts
  (`ContinuousLinearMap.IsSpectralProjection.comp_comp_of_retract`) and transport along ring
  homomorphisms of endomorphism algebras preserving the polynomial closure
  (`ContinuousLinearMap.IsSpectralProjection.map`).

## Main definitions

* `ContinuousLinearMap.IsSpectralProjection`: a spectral projection of `u` for `C` of order `h`.
* `ContinuousLinearMap.IsSpectralProjection.inverse`: the inverse of `C` on the complementary
  summand, extended by zero on `range E`.
* `ContinuousLinearMap.IsSpectralProjection.equivKer`: `C` as a continuous linear automorphism of
  the complementary summand `ker E`.

## Main results

* `ContinuousLinearMap.IsSpectralProjection.range_eq_ker`,
  `ContinuousLinearMap.IsSpectralProjection.range_pow_eq_ker`,
  `ContinuousLinearMap.IsSpectralProjection.isTopCompl_ker_range_pow`: stabilised kernel–range
  topological splitting.
* `ContinuousLinearMap.IsSpectralProjection.unique`: uniqueness of spectral projections.
* `ContinuousLinearMap.IsSpectralProjection.semiconj`,
  `ContinuousLinearMap.IsSpectralProjection.semiconj_inverse`,
  `ContinuousLinearMap.IsSpectralProjection.commute_of_commute`: functoriality and commutants.
* `ContinuousLinearMap.IsSpectralProjection.comp_comp_of_retract`,
  `ContinuousLinearMap.IsSpectralProjection.inverse_comp_comp_of_retract`: retract compression
  and its complementary inverse.
* `ContinuousLinearMap.IsSpectralProjection.map`,
  `ContinuousLinearMap.IsSpectralProjection.inverse_map`: transport along ring homomorphisms
  and its complementary inverse.

## References

* M. P. Drazin, *Pseudo-inverses in associative rings and semigroups*, Amer. Math. Monthly **65**
  (1958), 506–514.
* J.-P. Serre, *Endomorphismes complètement continus des espaces de Banach p-adiques*,
  Publ. Math. IHÉS **12** (1962), 69–85, §7.
* R. Coleman, *p-adic Banach spaces and families of modular forms*, Invent. Math. **127**
  (1997), 417–479, Appendix A, A4.
* C. Johansson and J. Newton, *Extended eigenvarieties for overconvergent cohomology*,
  arXiv:1604.07739, §2.2.
-/

public section

open scoped TauCeti.RingOpNorm

namespace ContinuousLinearMap

section Module

variable {R : Type*} [SeminormedCommRing R] [TauCeti.NormedRing.IsTate R]
  {M : Type*} [SeminormedAddCommGroup M] [Module R M] [IsBoundedSMul R M]

/-- A **spectral projection** of an endomorphism `u` of a seminormed `R`-module `M` for a spectral
operator `C` of order `h`: an idempotent `E` commuting with `u` and lying in the operator-norm
closure of the polynomials in `u`, such that `C ^ h * E = 0` and `C` is invertible on the
complementary summand `range (1 - E)`, with complementary inverse again in the closure of the
polynomials in `u`. -/
structure IsSpectralProjection (u C : M →L[R] M) (h : ℕ) (E : M →L[R] M) : Prop where
  /-- A spectral projection is idempotent. -/
  isIdempotentElem : IsIdempotentElem E
  /-- A spectral projection commutes with the operator `u`. -/
  commute : Commute u E
  /-- A spectral projection is an operator-norm limit of polynomials in `u`. -/
  mem_closure_adjoin : E ∈ closure (Algebra.adjoin R {u} : Set (M →L[R] M))
  /-- `C ^ h` vanishes on the range of a spectral projection. -/
  pow_mul_eq_zero : C ^ h * E = 0
  /-- `C` is invertible on the complementary summand, with inverse an operator-norm limit of
  polynomials in `u`. -/
  exists_inverse : ∃ w : M →L[R] M, C * w = 1 - E ∧ w * C = 1 - E ∧ E * w = 0 ∧ w * E = 0 ∧
    w ∈ closure (Algebra.adjoin R {u} : Set (M →L[R] M))

namespace IsSpectralProjection

variable {u C E : M →L[R] M} {h n : ℕ}

/-- A spectral projection of order `0` is zero. -/
theorem eq_zero_of_order_zero (hE : IsSpectralProjection u C 0 E) : E = 0 := by
  simpa using hE.pow_mul_eq_zero

/-- If the spectral operator `C` is invertible, any spectral projection for `C` is zero. -/
theorem eq_zero_of_isUnit (hE : IsSpectralProjection u C h E) (hC : IsUnit C) : E = 0 :=
  (hC.pow h).mul_right_eq_zero.mp hE.pow_mul_eq_zero

/-- Zero is a spectral projection for any invertible operator `C` whose inverse lies in the
operator-norm closure of `R[u]`. -/
theorem zero_of_isUnit (u : M →L[R] M) {C : M →L[R] M} {h : ℕ} (hC : IsUnit C)
    (hC_inv : ((hC.unit⁻¹ : (M →L[R] M)ˣ) : M →L[R] M) ∈
      closure (Algebra.adjoin R {u} : Set (M →L[R] M))) :
    IsSpectralProjection u C h 0 := by
  refine ⟨IsIdempotentElem.zero, Commute.zero_right u, subset_closure (zero_mem _), mul_zero _,
    ((hC.unit⁻¹ : (M →L[R] M)ˣ) : M →L[R] M), ?_, ?_, zero_mul _, mul_zero _, hC_inv⟩
  · simp
  · simp

/-- A spectral projection remains one when its nilpotence bound is increased. -/
theorem of_le (hE : IsSpectralProjection u C h E) (hn : h ≤ n) :
    IsSpectralProjection u C n E := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  refine { hE with pow_mul_eq_zero := ?_ }
  rw [add_comm h k, pow_add, mul_assoc, hE.pow_mul_eq_zero, mul_zero]

/-- Scaling the spectral operator `C` by a unit of the coefficient ring preserves spectral
projections. -/
theorem units_smul_spectral (hE : IsSpectralProjection u C h E) (c : Rˣ) :
    IsSpectralProjection u (c • C) h E := by
  obtain ⟨w, hw₁, hw₂, hw₃, hw₄, hw⟩ := hE.exists_inverse
  refine ⟨hE.isIdempotentElem, hE.commute, hE.mem_closure_adjoin, ?_,
    ⟨(↑c⁻¹ : R) • w, ?_, ?_, ?_, ?_, ?_⟩⟩
  · rw [Units.smul_def, smul_pow, smul_mul_assoc, hE.pow_mul_eq_zero, smul_zero]
  · rw [Units.smul_def, smul_mul_assoc, mul_smul_comm, smul_smul, Units.mul_inv, one_smul, hw₁]
  · rw [Units.smul_def, smul_mul_assoc, mul_smul_comm, smul_smul, Units.inv_mul, one_smul, hw₂]
  · rw [mul_smul_comm, hw₃, smul_zero]
  · rw [smul_mul_assoc, hw₄, smul_zero]
  · exact map_mem_closure (continuous_const_smul (↑c⁻¹ : R)) hw
      fun y hy ↦ (Algebra.adjoin R {u} : Subalgebra R _).smul_mem hy (↑c⁻¹ : R)

/-- Scaling the spectral operator `C` by a unit of the coefficient ring yields an equivalent
spectral-projection predicate. -/
@[simp]
theorem units_smul_spectral_iff (c : Rˣ) :
    IsSpectralProjection u (c • C) h E ↔ IsSpectralProjection u C h E :=
  ⟨fun h ↦ by simpa using h.units_smul_spectral c⁻¹, fun h ↦ h.units_smul_spectral c⟩

/-- A spectral projection commutes with its spectral operator `C`. -/
theorem commute_spectral (hE : IsSpectralProjection u C h E) : Commute C E := by
  obtain ⟨w, hw₁, hw₂, -, -, -⟩ := hE.exists_inverse
  have hCw : Commute C w := hw₁.trans hw₂.symm
  have h1 : Commute C (1 - E) := hw₂ ▸ hCw.mul_right (Commute.refl C)
  simpa using (Commute.one_right C).sub_right (R := M →L[R] M) h1

/-- `E * C ^ h = 0`, matching `pow_mul_eq_zero` by commutativity. -/
theorem mul_pow_eq_zero (hE : IsSpectralProjection u C h E) : E * C ^ h = 0 :=
  (hE.commute_spectral.pow_left h).eq.symm.trans hE.pow_mul_eq_zero

/-- The operator `u` preserves the kernel of its spectral projection. -/
theorem mapsTo_ker (hE : IsSpectralProjection u C h E) : Set.MapsTo u E.ker E.ker :=
  (Module.End.mem_invtSubmodule_iff_mapsTo _).mp
    ((ContinuousLinearMap.IsIdempotentElem.commute_iff
      hE.isIdempotentElem).mp hE.commute.symm).right

/-- The operator `u` preserves the range of its spectral projection. -/
theorem mapsTo_range (hE : IsSpectralProjection u C h E) : Set.MapsTo u E.range E.range :=
  (Module.End.mem_invtSubmodule_iff_mapsTo _).mp
    ((ContinuousLinearMap.IsIdempotentElem.commute_iff hE.isIdempotentElem).mp hE.commute.symm).left

/-- The spectral operator `C` preserves the kernel of its spectral projection. -/
theorem mapsTo_ker_spectral (hE : IsSpectralProjection u C h E) : Set.MapsTo C E.ker E.ker :=
  (Module.End.mem_invtSubmodule_iff_mapsTo _).mp
    ((ContinuousLinearMap.IsIdempotentElem.commute_iff hE.isIdempotentElem).mp
      hE.commute_spectral.symm).right

/-- The spectral operator `C` preserves the range of its spectral projection. -/
theorem mapsTo_range_spectral (hE : IsSpectralProjection u C h E) : Set.MapsTo C E.range E.range :=
  (Module.End.mem_invtSubmodule_iff_mapsTo _).mp
    ((ContinuousLinearMap.IsIdempotentElem.commute_iff hE.isIdempotentElem).mp
      hE.commute_spectral.symm).left

/-- The **complementary inverse** of a spectral projection: the inverse of `C` on the complementary
summand `range (1 - E)`, extended by zero on `range E`, chosen from
`IsSpectralProjection.exists_inverse`. -/
noncomputable def inverse (hE : IsSpectralProjection u C h E) : M →L[R] M :=
  hE.exists_inverse.choose

/-- The complementary inverse is a right inverse of `C` up to `1 - E`. -/
@[simp]
theorem spectral_mul_inverse (hE : IsSpectralProjection u C h E) : C * hE.inverse = 1 - E := by
  obtain ⟨hw, -, -, -, -⟩ := hE.exists_inverse.choose_spec
  exact hw

/-- The complementary inverse is a left inverse of `C` up to `1 - E`. -/
@[simp]
theorem inverse_mul_spectral (hE : IsSpectralProjection u C h E) : hE.inverse * C = 1 - E := by
  obtain ⟨-, hw, -, -, -⟩ := hE.exists_inverse.choose_spec
  exact hw

/-- The complementary inverse takes values in the kernel of the spectral projection. -/
@[simp]
theorem mul_inverse_eq_zero (hE : IsSpectralProjection u C h E) : E * hE.inverse = 0 := by
  obtain ⟨-, -, hw, -, -⟩ := hE.exists_inverse.choose_spec
  exact hw

/-- The complementary inverse vanishes on the range of the spectral projection. -/
@[simp]
theorem inverse_mul_eq_zero (hE : IsSpectralProjection u C h E) : hE.inverse * E = 0 := by
  obtain ⟨-, -, -, hw, -⟩ := hE.exists_inverse.choose_spec
  exact hw

/-- The complementary inverse is an operator-norm limit of polynomials in `u`. -/
theorem inverse_mem_closure_adjoin (hE : IsSpectralProjection u C h E) :
    hE.inverse ∈ closure (Algebra.adjoin R {u} : Set (M →L[R] M)) := by
  obtain ⟨-, -, -, -, hw⟩ := hE.exists_inverse.choose_spec
  exact hw

/-- The complementary inverse is the unique right inverse of `C` up to `1 - E` that takes values
in the kernel of the spectral projection. -/
theorem eq_inverse (hE : IsSpectralProjection u C h E) {w : M →L[R] M}
    (hw : C * w = 1 - E) (hEw : E * w = 0) : w = hE.inverse := by
  calc w = (1 - E) * w := by
        rw [sub_mul (α := M →L[R] M), one_mul, hEw, sub_zero w]
    _ = hE.inverse * (C * w) := by rw [← mul_assoc, hE.inverse_mul_spectral]
    _ = hE.inverse := by
        rw [hw, mul_sub (α := M →L[R] M), mul_one, hE.inverse_mul_eq_zero, sub_zero hE.inverse]

/-- Scaling the spectral operator `C` by a unit `c : Rˣ` scales the complementary inverse by
`c⁻¹`. -/
theorem inverse_units_smul_spectral (hE : IsSpectralProjection u C h E) (c : Rˣ) :
    (hE.units_smul_spectral c).inverse = c⁻¹ • hE.inverse := by
  refine ((hE.units_smul_spectral c).eq_inverse ?_ ?_).symm
  · rw [Units.smul_def, Units.smul_def, smul_mul_assoc, mul_smul_comm, smul_smul, Units.mul_inv,
      one_smul, hE.spectral_mul_inverse]
  · rw [Units.smul_def, mul_smul_comm, hE.mul_inverse_eq_zero, smul_zero]

/-- Increasing the nilpotence bound does not change the complementary inverse. -/
theorem inverse_of_le (hE : IsSpectralProjection u C h E) (hn : h ≤ n) :
    (hE.of_le hn).inverse = hE.inverse :=
  ((hE.of_le hn).eq_inverse hE.spectral_mul_inverse hE.mul_inverse_eq_zero).symm

/-- The complementary inverse preserves the kernel of the spectral projection. -/
theorem mapsTo_ker_inverse (hE : IsSpectralProjection u C h E) :
    Set.MapsTo hE.inverse E.ker E.ker := by
  intro x _
  apply LinearMap.mem_ker.mpr
  simpa only [coe_coe, mul_apply_eq_comp, zero_apply] using congr($(hE.mul_inverse_eq_zero) x)

/-- On the complementary summand, the complementary inverse is a left inverse of `C`. -/
theorem inverse_spectral_apply (hE : IsSpectralProjection u C h E) {x : M} (hx : x ∈ E.ker) :
    hE.inverse (C x) = x := by
  have hx' : E x = 0 := LinearMap.mem_ker.mp hx
  simpa only [mul_apply_eq_comp, sub_apply, one_apply_eq_self, hx', sub_zero] using
    congr($(hE.inverse_mul_spectral) x)

/-- On the complementary summand, the complementary inverse is a right inverse of `C`. -/
theorem spectral_apply_inverse (hE : IsSpectralProjection u C h E) {x : M} (hx : x ∈ E.ker) :
    C (hE.inverse x) = x := by
  have hx' : E x = 0 := LinearMap.mem_ker.mp hx
  simpa only [mul_apply_eq_comp, sub_apply, one_apply_eq_self, hx', sub_zero] using
    congr($(hE.spectral_mul_inverse) x)

/-- **The range of a spectral projection is `ker (C ^ h)`.** -/
theorem range_eq_ker (hE : IsSpectralProjection u C h E) :
    LinearMap.range (E : M →ₗ[R] M) = LinearMap.ker ((C ^ h : M →L[R] M) : M →ₗ[R] M) := by
  obtain ⟨w, hw, hw', -⟩ := hE.exists_inverse
  have hCw : Commute C w := hw.trans hw'.symm
  have h1 := hE.isIdempotentElem.one_sub_eq_pow_mul_pow (A := M →L[R] M) hE.pow_mul_eq_zero hw hw'
  rw [(hCw.pow_pow h h).eq] at h1
  ext x
  simp only [LinearMap.mem_range, LinearMap.mem_ker, coe_coe]
  refine ⟨?_, fun hx ↦ ⟨x, ?_⟩⟩
  · rintro ⟨y, rfl⟩
    simpa only [mul_apply_eq_comp, zero_apply] using congr($(hE.pow_mul_eq_zero) y)
  · have := congr($h1 x)
    simp only [sub_apply, one_apply_eq_self, mul_apply_eq_comp, hx, map_zero, sub_eq_zero] at this
    exact this.symm

/-- The kernels of the powers of `C` stabilise at the nilpotence bound of a spectral projection. -/
theorem ker_pow_eq (hE : IsSpectralProjection u C h E) (hn : h ≤ n) :
    LinearMap.ker ((C ^ n : M →L[R] M) : M →ₗ[R] M) =
      LinearMap.ker ((C ^ h : M →L[R] M) : M →ₗ[R] M) := by
  rw [← (hE.of_le hn).range_eq_ker, hE.range_eq_ker]

/-- The range of every sufficiently large power of `C` is the kernel of its spectral projection. -/
theorem range_pow_eq_ker (hE : IsSpectralProjection u C h E) (hn : h ≤ n) :
    LinearMap.range ((C ^ n : M →L[R] M) : M →ₗ[R] M) = LinearMap.ker (E : M →ₗ[R] M) := by
  have hEn := hE.of_le hn
  have h1 := _root_.IsIdempotentElem.one_sub_eq_pow_mul_pow hE.isIdempotentElem
    (A := M →L[R] M) hEn.pow_mul_eq_zero hE.spectral_mul_inverse hE.inverse_mul_spectral
  ext x
  simp only [LinearMap.mem_range, LinearMap.mem_ker, coe_coe]
  refine ⟨?_, fun hx ↦ ⟨(hE.inverse ^ n) x, ?_⟩⟩
  · rintro ⟨y, rfl⟩
    simpa only [mul_apply_eq_comp, zero_apply] using congr($(hEn.mul_pow_eq_zero) y)
  · simpa only [mul_apply_eq_comp, sub_apply, one_apply_eq_self, hx, sub_zero] using
      congr($h1 x).symm

/-- The ranges of the powers of `C` stabilise at the nilpotence bound of a spectral projection. -/
theorem range_pow_eq (hE : IsSpectralProjection u C h E) (hn : h ≤ n) :
    LinearMap.range ((C ^ n : M →L[R] M) : M →ₗ[R] M) =
      LinearMap.range ((C ^ h : M →L[R] M) : M →ₗ[R] M) := by
  rw [hE.range_pow_eq_ker hn, hE.range_pow_eq_ker le_rfl]

/-- **`ker (C ^ n)` and `range (C ^ n)` are topological complements** for every `n ≥ h`. -/
theorem isTopCompl_ker_range_pow (hE : IsSpectralProjection u C h E) (hn : h ≤ n) :
    (LinearMap.ker ((C ^ n : M →L[R] M) : M →ₗ[R] M)).IsTopCompl
      (LinearMap.range ((C ^ n : M →L[R] M) : M →ₗ[R] M)) := by
  rw [← (hE.of_le hn).range_eq_ker, hE.range_pow_eq_ker hn]
  exact ContinuousLinearMap.IsIdempotentElem.isTopCompl hE.isIdempotentElem

/-- Every stabilised range of `C` is closed whenever `M` is `T₁` (in particular, normed). -/
theorem isClosed_range_pow [T1Space M] (hE : IsSpectralProjection u C h E) (hn : h ≤ n) :
    IsClosed (LinearMap.range ((C ^ n : M →L[R] M) : M →ₗ[R] M) : Set M) := by
  rw [hE.range_pow_eq_ker hn]
  exact E.isClosed_ker

/-- The spectral operator `C` as a continuous linear automorphism of the complementary summand
`ker E`, identified with every stabilised range by `range_pow_eq_ker`. Its inverse is the
restriction of `IsSpectralProjection.inverse`. -/
noncomputable def equivKer (hE : IsSpectralProjection u C h E) : E.ker ≃L[R] E.ker :=
  ContinuousLinearEquiv.ofContinuousLinearMap
    (C.restrict (fun _ hx ↦ hE.mapsTo_ker_spectral hx))
    (hE.inverse.restrict (fun _ hx ↦ hE.mapsTo_ker_inverse hx))
    (ContinuousLinearMap.ext fun x ↦ Subtype.ext (hE.spectral_apply_inverse x.property))
    (ContinuousLinearMap.ext fun x ↦ Subtype.ext (hE.inverse_spectral_apply x.property))

/-- The complementary automorphism acts by the spectral operator `C`. -/
@[simp]
theorem coe_equivKer_apply (hE : IsSpectralProjection u C h E) (x : E.ker) :
    (hE.equivKer x : M) = C x :=
  (rfl)

/-- The inverse complementary automorphism acts by `IsSpectralProjection.inverse`. -/
@[simp]
theorem coe_equivKer_symm_apply (hE : IsSpectralProjection u C h E) (x : E.ker) :
    (hE.equivKer.symm x : M) = hE.inverse x :=
  (rfl)

/-- **Uniqueness of spectral projections.** Two spectral projections for the same spectral operator
`C` are equal, even for different ambient operators or nilpotence bounds. -/
theorem unique {v E' : M →L[R] M} {k : ℕ} (hE : IsSpectralProjection u C h E)
    (hE' : IsSpectralProjection v C k E') : E = E' := by
  have hEn := hE.of_le (Nat.le_max_left h k)
  have hE'n := hE'.of_le (Nat.le_max_right h k)
  obtain ⟨w, hw, hw', -⟩ := hE.exists_inverse
  obtain ⟨w', hw₂, hw₂', -⟩ := hE'.exists_inverse
  exact hE.isIdempotentElem.eq_of_pow_mul_eq_zero hE'.isIdempotentElem hEn.pow_mul_eq_zero
    hE'n.pow_mul_eq_zero hw hw' hw₂ hw₂'

end IsSpectralProjection

end Module

section Intertwining

variable {R M N : Type*} [SeminormedCommRing R] [TauCeti.NormedRing.IsTate R]
  [SeminormedAddCommGroup M] [Module R M] [IsBoundedSMul R M]
  [SeminormedAddCommGroup N] [Module R N] [IsBoundedSMul R N]
  {u C E : M →L[R] M} {v D F : N →L[R] N} {h k : ℕ}

namespace IsSpectralProjection

/-- **Functoriality of spectral projections.** A linear map intertwining the spectral operators
`C` and `D` intertwines their spectral projections, even when the nilpotence bounds differ.
Continuity of the intertwiner is unnecessary. -/
theorem semiconj (hE : IsSpectralProjection u C h E) (hF : IsSpectralProjection v D k F)
    (f : M →ₗ[R] N) (hf : Function.Semiconj f C D) :
    Function.Semiconj f E F := by
  let n := max h k
  have hEn := hE.of_le (Nat.le_max_left h k)
  have hFn := hF.of_le (Nat.le_max_right h k)
  have hfn : Function.Semiconj f (C ^ n : M →L[R] M) (D ^ n : N →L[R] N) := by
    simpa only [FunLike.coe_pow_eq_iterate] using hf.iterate_right n
  intro x
  have hfixed : F (f (E x)) = f (E x) := by
    apply (LinearMap.IsIdempotentElem.mem_range_iff
      (ContinuousLinearMap.IsIdempotentElem.toLinearMap hF.isIdempotentElem)).mp
    rw [hFn.range_eq_ker]
    apply LinearMap.mem_ker.mpr
    simp only [coe_coe]
    rw [← hfn]
    have hz := congr($(hEn.pow_mul_eq_zero) x)
    simpa only [mul_apply_eq_comp, zero_apply, map_zero, coe_coe] using congr(f $hz)
  have hzero : F (f (x - E x)) = 0 := by
    have hx : x - E x ∈ E.ker := by
      rw [LinearMap.IsIdempotentElem.ker_eq_range_one_sub
        (ContinuousLinearMap.IsIdempotentElem.toLinearMap hE.isIdempotentElem)]
      exact ⟨x, rfl⟩
    rw [← hE.range_pow_eq_ker (Nat.le_max_left h k)] at hx
    obtain ⟨y, hy⟩ := hx
    simp only [coe_coe] at hy
    apply LinearMap.mem_ker.mp
    rw [← hF.range_pow_eq_ker (Nat.le_max_right h k)]
    exact ⟨f y, by simp only [coe_coe]; rw [← hfn y, hy]⟩
  rw [map_sub, map_sub, hfixed, sub_eq_zero] at hzero
  exact hzero.symm

/-- An intertwiner of spectral operators sends the spectral summand `range E` into `range F`. -/
theorem mapsTo_range_of_semiconj (hE : IsSpectralProjection u C h E)
    (hF : IsSpectralProjection v D k F) (f : M →ₗ[R] N) (hf : Function.Semiconj f C D) :
    Set.MapsTo f E.range F.range := by
  rintro _ ⟨x, rfl⟩
  exact ⟨f x, (hE.semiconj hF f hf x).symm⟩

/-- An intertwiner of spectral operators sends the complementary summand `ker E` into `ker F`. -/
theorem mapsTo_ker_of_semiconj (hE : IsSpectralProjection u C h E)
    (hF : IsSpectralProjection v D k F) (f : M →ₗ[R] N) (hf : Function.Semiconj f C D) :
    Set.MapsTo f E.ker F.ker := by
  intro x hx
  apply LinearMap.mem_ker.mpr
  simp only [coe_coe]
  have hx' : E x = 0 := LinearMap.mem_ker.mp hx
  rw [← hE.semiconj hF f hf, hx', map_zero]

/-- Intertwiners of spectral operators carry their complementary inverses to one another. -/
theorem semiconj_inverse (hE : IsSpectralProjection u C h E) (hF : IsSpectralProjection v D k F)
    (f : M →ₗ[R] N) (hf : Function.Semiconj f C D) :
    Function.Semiconj f hE.inverse hF.inverse := by
  have hEF := hE.semiconj hF f hf
  intro x
  have hker : f (hE.inverse x) ∈ F.ker := by
    apply LinearMap.mem_ker.mpr
    simp only [coe_coe]
    rw [← hEF]
    have hz := congr($(hE.mul_inverse_eq_zero) x)
    simpa only [mul_apply_eq_comp, zero_apply, map_zero] using congr(f $hz)
  calc f (hE.inverse x) = hF.inverse (D (f (hE.inverse x))) :=
        (hF.inverse_spectral_apply hker).symm
    _ = hF.inverse (f (C (hE.inverse x))) := by rw [hf]
    _ = hF.inverse (f (x - E x)) :=
        congrArg (fun y ↦ hF.inverse (f y)) (congr($(hE.spectral_mul_inverse) x))
    _ = hF.inverse (f x - F (f x)) := by rw [map_sub, hEF x]
    _ = hF.inverse (f x) := by
        rw [map_sub, ← mul_apply_eq_comp, hF.inverse_mul_eq_zero, zero_apply, sub_zero]

/-- A bounded operator commuting with `C` commutes with every spectral projection for `C`. -/
theorem commute_of_commute (hE : IsSpectralProjection u C h E) {w : M →L[R] M}
    (hw : Commute w C) : Commute w E :=
  ext fun x ↦ hE.semiconj hE w.toLinearMap (fun y ↦ congr($(hw.eq) y)) x

/-- A bounded operator commuting with `C` commutes with the complementary inverse of every spectral
projection for `C`. -/
theorem commute_inverse_of_commute (hE : IsSpectralProjection u C h E) {w : M →L[R] M}
    (hw : Commute w C) : Commute w hE.inverse :=
  ext fun x ↦ hE.semiconj_inverse hE w.toLinearMap (fun y ↦ congr($(hw.eq) y)) x

end IsSpectralProjection

end Intertwining

section Retract

variable {R M N : Type*} [NormedCommRing R] [TauCeti.NormedRing.IsTate R]
  [SeminormedAddCommGroup M] [Module R M] [IsBoundedSMul R M]
  [SeminormedAddCommGroup N] [Module R N] [IsBoundedSMul R N]
  {i : M →L[R] N} {r : N →L[R] M} {u : M →L[R] M}

/-- **Compression of spectral projections along a retract.** Let `r ∘ i = id` present `M` as a
retract of a seminormed module `N`, and suppose `r` and `i` intertwine spectral operators `D` on
`N` and `C` on `M`. If `E` is a spectral projection of the extension `i ∘ u ∘ r` for `D`, then
`r ∘ E ∘ i` is a spectral projection of `u` for `C`. -/
theorem IsSpectralProjection.comp_comp_of_retract (hri : r.comp i = .id R M)
    {C : M →L[R] M} {D : N →L[R] N} {h : ℕ} {E : N →L[R] N}
    (hr : Function.Semiconj (r : N →ₗ[R] M) D C)
    (hi : Function.Semiconj (i : M →ₗ[R] N) C D)
    (hE : IsSpectralProjection (i.comp (u.comp r)) D h E) :
    IsSpectralProjection u C h (r.comp (E.comp i)) := by
  have hri' (x : M) : r (i x) = x := by simpa using DFunLike.congr_fun hri x
  have hrh : Function.Semiconj (r : N →ₗ[R] M) (D ^ h : N →L[R] N) (C ^ h : M →L[R] M) := by
    simpa only [FunLike.coe_pow_eq_iterate] using hr.iterate_right h
  have hir_comm : Commute (i.comp r) D := by
    ext y
    simp only [mul_apply_eq_comp, comp_apply]
    exact (congrArg i (hr y)).trans (hi (r y))
  have hE' (y : N) : i (r (E y)) = E (i (r y)) :=
    congr($(hE.commute_of_commute hir_comm) y)
  have hw' (y : N) : i (r (hE.inverse y)) = hE.inverse (i (r y)) :=
    congr($(hE.commute_inverse_of_commute hir_comm) y)
  have hEE (y : N) : E (E y) = E y := congr($hE.isIdempotentElem.eq y)
  have hEv (y : N) : E (i (u (r y))) = i (u (r (E y))) := congr($hE.commute.eq y).symm
  have hpow (y : N) : (D ^ h) (E y) = 0 := congr($hE.pow_mul_eq_zero y)
  refine ⟨?_, ?_, comp_comp_mem_closure_adjoin hri hE.mem_closure_adjoin, ?_,
    ⟨r.comp (hE.inverse.comp i), ?_, ?_, ?_, ?_,
      comp_comp_mem_closure_adjoin hri hE.inverse_mem_closure_adjoin⟩⟩
  · ext x; simp [hE', hri', hEE]
  · ext x; simpa [hri'] using congr(r $(hEv (i x))).symm
  · ext x; simpa [hpow] using (hrh (E (i x))).symm
  · ext x
    simpa [hri'] using
      (hr (hE.inverse (i x))).symm.trans congr(r $(congr($(hE.spectral_mul_inverse) (i x))))
  · ext x
    have hiCx : i (C x) = D (i x) := hi x
    simpa only [mul_apply_eq_comp, comp_apply, sub_apply, one_apply_eq_self, map_sub, hri',
      hiCx] using congr(r $(congr($(hE.inverse_mul_spectral) (i x))))
  · ext x
    simp only [mul_apply_eq_comp, comp_apply, hw', hri', zero_apply]
    rw [← mul_apply_eq_comp, hE.mul_inverse_eq_zero, zero_apply, map_zero]
  · ext x
    simp only [mul_apply_eq_comp, comp_apply, hE', hri', zero_apply]
    rw [← mul_apply_eq_comp, hE.inverse_mul_eq_zero, zero_apply, map_zero]

/-- The complementary inverse of the retract-compressed spectral projection is the retract
compression `r ∘ hE.inverse ∘ i` of the original complementary inverse. -/
theorem IsSpectralProjection.inverse_comp_comp_of_retract (hri : r.comp i = .id R M)
    {C : M →L[R] M} {D : N →L[R] N} {h : ℕ} {E : N →L[R] N}
    (hr : Function.Semiconj (r : N →ₗ[R] M) D C)
    (hi : Function.Semiconj (i : M →ₗ[R] N) C D)
    (hE : IsSpectralProjection (i.comp (u.comp r)) D h E) :
    (hE.comp_comp_of_retract hri hr hi).inverse = r.comp (hE.inverse.comp i) := by
  ext x
  have hri' : r (i x) = x := by simpa using DFunLike.congr_fun hri x
  have h := hE.semiconj_inverse (hE.comp_comp_of_retract hri hr hi) r.toLinearMap hr (i x)
  simpa only [comp_apply, coe_coe, hri'] using h.symm

end Retract

section Map

variable {R S M N : Type*}
  [SeminormedCommRing R] [TauCeti.NormedRing.IsTate R]
  [SeminormedAddCommGroup M] [Module R M] [IsBoundedSMul R M]
  [SeminormedCommRing S] [TauCeti.NormedRing.IsTate S]
  [SeminormedAddCommGroup N] [Module S N] [IsBoundedSMul S N]

/-- **Spectral projections under a ring homomorphism of endomorphism algebras.** A ring
homomorphism `φ` sending the operator-norm closure of `R[u]` into the closure of `S[φ u]` carries
a spectral projection of `u` for `C` to one of `φ u` for `φ C`. -/
theorem IsSpectralProjection.map {u C E : M →L[R] M} {h : ℕ}
    (hE : IsSpectralProjection u C h E) (φ : (M →L[R] M) →+* (N →L[S] N))
    (hφ : ∀ {v}, v ∈ closure (Algebra.adjoin R {u} : Set (M →L[R] M)) →
      φ v ∈ closure (Algebra.adjoin S {φ u} : Set (N →L[S] N))) :
    IsSpectralProjection (φ u) (φ C) h (φ E) := by
  obtain ⟨w, hw₁, hw₂, hw₃, hw₄, hw⟩ := hE.exists_inverse
  refine ⟨hE.isIdempotentElem.map φ, hE.commute.map φ, hφ hE.mem_closure_adjoin, ?_,
    ⟨φ w, ?_, ?_, ?_, ?_, hφ hw⟩⟩
  · simpa only [map_mul, map_pow, map_zero] using congrArg φ hE.pow_mul_eq_zero
  · simpa only [map_mul, map_sub, map_one] using congrArg φ hw₁
  · simpa only [map_mul, map_sub, map_one] using congrArg φ hw₂
  · simpa only [map_mul, map_zero] using congrArg φ hw₃
  · simpa only [map_mul, map_zero] using congrArg φ hw₄

/-- The complementary inverse of any spectral projection `hF` whose spectral operator and
projector match `φ C` and `φ E` under a ring homomorphism `φ` is the image `φ hE.inverse` of the
original complementary inverse. -/
theorem IsSpectralProjection.inverse_map {u C E : M →L[R] M} {h : ℕ}
    (hE : IsSpectralProjection u C h E) (φ : (M →L[R] M) →+* (N →L[S] N))
    {u' C' E' : N →L[S] N} {k : ℕ} (hF : IsSpectralProjection u' C' k E')
    (hC : C' = φ C) (hE' : E' = φ E) :
    hF.inverse = φ hE.inverse := by
  refine (hF.eq_inverse ?_ ?_).symm
  · simpa only [hC, hE', map_mul, map_sub, map_one] using congrArg φ hE.spectral_mul_inverse
  · simpa only [hE', map_mul, map_zero] using congrArg φ hE.mul_inverse_eq_zero

end Map

end ContinuousLinearMap
