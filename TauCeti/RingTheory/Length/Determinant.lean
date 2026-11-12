/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.RingTheory.OrderOfVanishing.Basic
public import TauCeti.LinearAlgebra.Matrix.Transvection
public import TauCeti.RingTheory.Length.Endomorphism
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import TauCeti.LinearAlgebra.Dimension.Localization
import TauCeti.LinearAlgebra.Matrix.Diagonal.Length
import TauCeti.RingTheory.OrderOfVanishing

/-!
# Cokernel length and determinant

Let `A` be a Noetherian domain of Krull dimension at most one, for example a principal ideal
domain or a one-dimensional local ring of a variety. For a square matrix `ψ` over `A` with nonzero
determinant, the cokernel of `ψ` on `Aⁿ` has length `ord_A (det ψ)`
(`Matrix.length_quotient_range_mulVecLin_eq_ord_det`; Fulton, *Intersection Theory*,
Appendix A.2, for free modules). Applied to a trace Gram matrix, this is the linear algebra input
to the discriminant-length formula; applied to multiplication by an element of a finite free
`A`-algebra, it computes the order of a norm.

Both sides are additive in `ψ` (`TauCeti.length_quotient_range_comp` and `Ring.ord_mul`), and
they agree on diagonal matrices (`Matrix.length_quotient_range_diagonal_mulVecLin`, which
holds over any commutative ring) and on transvections. Since `A` need not have a Smith normal
form, the comparison rests on a rigidity statement,
`Matrix.eq_zero_of_map_mul_of_diagonal_of_transvection`: a function on nonsingular
matrices over a domain `A` that is additive under products and vanishes on nonsingular diagonal
matrices and on transvections vanishes identically. To prove it, extend the function to
nonsingular matrices over the fraction field `K`, by evaluating at any integral multiple `sN` of
`N` (the value does not depend on `s`, since it vanishes on scalars). Over `K` every nonsingular
matrix is a product of transvections and a diagonal matrix, and a transvection with entry `x / t`
is the conjugate of the one with entry `x` by a diagonal matrix.

## References

* W. Fulton, *Intersection Theory*, Appendix A.2.
* J.-P. Serre, *Local Fields*, Chapter III, Section 3 (discriminants and differents).
-/
public section

open Matrix

namespace TauCeti

variable {A ι : Type*} [CommRing A] [IsDomain A] [Fintype ι] [DecidableEq ι]

section KrullDimLE

variable [IsNoetherianRing A] [Ring.KrullDimLE 1 A]

/-- Over a Noetherian domain of dimension at most one, a matrix with nonzero determinant has a
cokernel of finite length: it is a quotient of the cokernel of multiplication by the determinant,
since `ψ * adj ψ = det ψ • 1`. -/
theorem _root_.Matrix.length_quotient_range_mulVecLin_ne_top {ψ : Matrix ι ι A}
    (hψ : ψ.det ≠ 0) :
    Module.length A ((ι → A) ⧸ LinearMap.range ψ.mulVecLin) ≠ ⊤ := by
  have hle : LinearMap.range (LinearMap.lsmul A (ι → A) ψ.det) ≤
      LinearMap.range ψ.mulVecLin := by
    rintro _ ⟨v, rfl⟩
    exact ⟨ψ.adjugate *ᵥ v, by
      rw [mulVecLin_apply, mulVec_mulVec, mul_adjugate, smul_mulVec, one_mulVec]; rfl⟩
  refine ne_top_of_le_ne_top ?_ (length_quotient_anti hle)
  rw [length_quotient_lsmul_pi ι ψ.det]
  exact WithTop.mul_ne_top (ENat.natCast_ne_top _)
    (Ring.ord_ne_top (mem_nonZeroDivisors_of_ne_zero hψ))

/-- **Cokernel length and determinant** (Fulton, *Intersection Theory*, Appendix A.2, for free
modules). Over a Noetherian domain `A` of dimension at most one, such as a principal ideal domain,
the cokernel of a square matrix with nonzero determinant has length `ord_A (det ψ)`. -/
theorem _root_.Matrix.length_quotient_range_mulVecLin_eq_ord_det (ψ : Matrix ι ι A)
    (hψ : ψ.det ≠ 0) :
    Module.length A ((ι → A) ⧸ LinearMap.range ψ.mulVecLin) = Ring.ord A ψ.det := by
  let g : Matrix ι ι A → ℤ := fun M ↦
    (Module.length A ((ι → A) ⧸ LinearMap.range M.mulVecLin)).toNat - (Ring.ord A M.det).toNat
  have hg : g ψ = 0 := by
    refine eq_zero_of_map_mul_of_diagonal_of_transvection g (fun M N hM hN ↦ ?_)
      (fun d hd ↦ ?_) (fun i j hij x ↦ ?_) hψ
    · have hNnz := mem_nonZeroDivisors_of_ne_zero hN
      have hMinj : Function.Injective M.mulVecLin := mulVec_injective_of_det_ne_zero hM
      have he : Module.length A ((ι → A) ⧸ LinearMap.range (M * N).mulVecLin) =
          Module.length A ((ι → A) ⧸ LinearMap.range M.mulVecLin) +
            Module.length A ((ι → A) ⧸ LinearMap.range N.mulVecLin) := by
        rw [mulVecLin_mul]
        exact length_quotient_range_comp hMinj N.mulVecLin
      simp only [g, he, det_mul, _root_.Ring.ord_mul A hNnz,
        ENat.toNat_add (length_quotient_range_mulVecLin_ne_top hM)
          (length_quotient_range_mulVecLin_ne_top hN),
        ENat.toNat_add (Ring.ord_ne_top (mem_nonZeroDivisors_of_ne_zero hM))
          (Ring.ord_ne_top hNnz)]
      push_cast
      ring
    · simp only [g, length_quotient_range_diagonal_mulVecLin, det_diagonal,
        Ring.ord_prod fun i _ ↦ mem_nonZeroDivisors_of_ne_zero (hd i), sub_self]
    · have hsurj : LinearMap.range (transvection i j x).mulVecLin = ⊤ :=
        LinearMap.range_eq_top.2 (mulVec_surjective_iff_isUnit.2
          ((isUnit_iff_isUnit_det _).2 (by rw [det_transvection_of_ne _ _ hij]; exact isUnit_one)))
      have h0 : Module.length A ((ι → A) ⧸ LinearMap.range (transvection i j x).mulVecLin) = 0 :=
        Module.length_eq_zero_iff.2 (Submodule.Quotient.subsingleton_iff.2 hsurj)
      simp only [g, h0, det_transvection_of_ne _ _ hij, Ring.ord_one, ENat.toNat_zero, sub_self]
  have h := congrArg ((↑) : ℕ → ℕ∞) (Int.ofNat_inj.1 (sub_eq_zero.1 hg))
  rwa [ENat.natCast_toNat (length_quotient_range_mulVecLin_ne_top hψ),
    ENat.natCast_toNat (Ring.ord_ne_top (mem_nonZeroDivisors_of_ne_zero hψ))] at h

end KrullDimLE

section Lattice

variable {A K V : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A] [Ring.KrullDimLE 1 A]
  [Field K] [Algebra A K] [IsFractionRing A K]
  [AddCommGroup V] [Module K V] [Module A V] [IsScalarTower A K V]

/-- **The order of a determinant is a cokernel length** (Fulton, *Intersection Theory*,
Appendix A.2). Let `A` be a Noetherian domain of dimension at most one with fraction field `K`, let
`M` be a finitely generated `A`-submodule spanning a `K`-vector space `V`, and let `φ` be a
nonsingular `K`-linear endomorphism of `V` preserving `M`. If `M ⧸ φ(M)` has length `n`, then
`det φ` has order `n`. -/
theorem _root_.LinearMap.ordFrac_det_eq_coe_of_length_eq (φ : V →ₗ[K] V) (M : Submodule A V)
    (hfg : M.FG) (hM : Submodule.span K (M : Set V) = ⊤) (hφM : ∀ x ∈ M, φ x ∈ M)
    (hφ : LinearMap.det φ ≠ 0) {n : ℕ}
    (hn : Module.length A (M ⧸ LinearMap.range ((φ.restrictScalars A).restrict hφM)) = n) :
    Ring.ordFrac A (LinearMap.det φ) = Multiplicative.ofAdd (n : ℤ) := by
  classical
  have hinjK : Function.Injective (algebraMap A K) := IsFractionRing.injective A K
  have : Module.Finite A M := Module.Finite.iff_fg.mpr hfg
  have : Module.IsTorsionFree A V := Module.IsTorsionFree.comap (algebraMap A K)
    (fun r hr ↦ isRegular_iff_ne_zero.2 ((map_ne_zero_iff _ hinjK).2
      (isRegular_iff_ne_zero.1 hr))) (fun r m ↦ algebraMap_smul K r m)
  have : Module.IsTorsionFree A M :=
    Function.Injective.moduleIsTorsionFree M.subtype Subtype.val_injective fun _ _ ↦ rfl
  obtain ⟨r, v, c, hv, hc, hcM, hrank⟩ := exists_linearIndependent_smul_mem_span (A := A) (M := M)
  set F : Submodule A M := Submodule.span A (Set.range v)
  let bF : Module.Basis (Fin r) A F := Module.Basis.span hv
  -- The family `v` is a `K`-basis of `V`.
  let w : Fin r → V := fun i ↦ (v i : V)
  have hw : LinearIndependent K w :=
    (LinearIndependent.iff_fractionRing A K).1 (hv.map' M.subtype M.ker_subtype)
  have hcw : ∀ x ∈ M, c • x ∈ Submodule.span A (Set.range w) := fun x hx ↦ by
    have h := Submodule.mem_map_of_mem (f := M.subtype) (hcM ⟨x, hx⟩)
    rwa [Submodule.map_span, ← Set.range_comp] at h
  have hspan : ⊤ ≤ Submodule.span K (Set.range w) := by
    rw [← hM, Submodule.span_le]
    intro x hx
    rw [SetLike.mem_coe]
    have h := Submodule.span_le_restrictScalars A K _ (hcw x hx)
    rw [Submodule.restrictScalars_mem, ← algebraMap_smul K c x] at h
    have hcK : algebraMap A K c ≠ 0 := (map_ne_zero_iff _ hinjK).2 hc
    simpa only [inv_smul_smul₀ hcK] using Submodule.smul_mem _ (algebraMap A K c)⁻¹ h
  let bK : Module.Basis (Fin r) K V := Module.Basis.mk hw hspan
  have : Module.Free K V := Module.Free.of_basis bK
  have : Module.Finite K V := Module.Finite.of_basis bK
  -- The endomorphisms `φ` of `M`, `cφ` of `M`, and `cφ` of `F`.
  let φM : M →ₗ[A] M := (φ.restrictScalars A).restrict hφM
  have hφinj : Function.Injective φ :=
    ((Module.End.isUnit_iff φ).1 ((LinearMap.isUnit_iff_isUnit_det φ).2 hφ.isUnit)).1
  have hφMinj : Function.Injective φM := fun x y h ↦ Subtype.ext (hφinj (congrArg Subtype.val h))
  let χ : M →ₗ[A] M := LinearMap.lsmul A M c ∘ₗ φM
  have hcinj : Function.Injective (LinearMap.lsmul A M c) := smul_right_injective M hc
  have hχinj : Function.Injective χ := by
    rw [LinearMap.coe_comp]; exact hcinj.comp hφMinj
  have hχF : ∀ x ∈ F, χ x ∈ F := fun x _ ↦ hcM (φM x)
  let ψ : F →ₗ[A] F := χ.restrict hχF
  have hfin : IsFiniteLength A (M ⧸ F) := by
    refine isFiniteLength_of_nonZeroDivisor_mem_annihilator (x := c) ?_
      (mem_nonZeroDivisors_of_ne_zero hc)
    rw [Module.mem_annihilator]
    rintro ⟨m⟩
    exact (Submodule.Quotient.mk_eq_zero F).2 (hcM m)
  -- The matrix of `ψ` is that of `cφ` over `K`.
  have hbK : ∀ k, bK k = w k := fun k ↦ Module.Basis.mk_apply hw hspan k
  have hbF : ∀ k, ((bF k : M) : V) = w k := fun k ↦
    congrArg (fun x : F ↦ ((x : M) : V)) (Module.Basis.span_apply hv k)
  have hmat : (LinearMap.toMatrix bF bF ψ).map (algebraMap A K) =
      LinearMap.toMatrix bK bK (algebraMap A K c • φ) := by
    ext i j
    have hsum := congrArg (fun x : F ↦ ((x : M) : V)) (bF.sum_repr (ψ (bF j)))
    simp only [Submodule.coe_sum, Submodule.coe_smul] at hsum
    have hψ : ((ψ (bF j) : M) : V) = c • φ (w j) := by
      -- Unfold ψ = χ|F, χ = c • φM, and φM = φ|M through both subtype coercions.
      -- Rewriting coe_restrict_apply fails at φM: hφM is stated for φ, while the
      -- restriction uses φ.restrictScalars A, so matching needs definitional reduction.
      change c • φ ((bF j : M) : V) = _
      rw [hbF]
    have hterm : ∀ k, bF.repr (ψ (bF j)) k • ((bF k : M) : V) =
        algebraMap A K (bF.repr (ψ (bF j)) k) • bK k := fun k ↦ by
      rw [hbK, hbF, algebraMap_smul]
    rw [map_apply, LinearMap.toMatrix_apply, LinearMap.toMatrix_apply, LinearMap.smul_apply,
      algebraMap_smul, hbK, ← hψ, ← hsum, Finset.sum_congr rfl fun k _ ↦ hterm k,
      bK.repr_sum_self]
  have hdet : algebraMap A K (LinearMap.toMatrix bF bF ψ).det =
      algebraMap A K c ^ r * LinearMap.det φ := by
    rw [RingHom.map_det, RingHom.mapMatrix_apply, hmat, LinearMap.det_toMatrix, LinearMap.det_smul,
      Module.finrank_eq_card_basis bK, Fintype.card_fin]
  set D := (LinearMap.toMatrix bF bF ψ).det
  have hD : D ≠ 0 := fun h ↦ by
    rw [h, map_zero] at hdet
    exact mul_ne_zero (pow_ne_zero _ ((map_ne_zero_iff _ hinjK).2 hc)) hφ hdet.symm
  -- The lengths.
  obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.1 (Ring.ord_ne_top (mem_nonZeroDivisors_of_ne_zero hc))
  have hlen : Ring.ord A D = (r * k + n : ℕ) := by
    rw [← Matrix.length_quotient_range_mulVecLin_eq_ord_det _ hD,
      ← Module.Basis.length_quotient_range_eq_length_quotient_range_toMatrix,
      length_quotient_range_restrict hχinj hχF hfin,
      length_quotient_range_comp hcinj, length_quotient_lsmul_eq_finrank_mul_ord hc, hn, hrank,
      ← hk]
    push_cast
    rfl
  have hcr : Ring.ord A (c ^ r) = (r * k : ℕ) := by
    rw [Ring.ord_pow (mem_nonZeroDivisors_of_ne_zero hc), ← hk]
    push_cast
    rfl
  have h := congrArg (Ring.ordFrac A) hdet
  rw [Ring.ordFrac_eq_ord A hD, ← map_pow, map_mul, Ring.ordFrac_eq_ord A (pow_ne_zero _ hc),
    Ring.ordMonoidWithZeroHom_eq_coe A (mem_nonZeroDivisors_of_ne_zero hD) hlen,
    Ring.ordMonoidWithZeroHom_eq_coe A (mem_nonZeroDivisors_of_ne_zero (pow_ne_zero _ hc)) hcr] at h
  refine mul_left_cancel₀ (WithZero.coe_ne_zero (a := Multiplicative.ofAdd ((r * k : ℕ) : ℤ)))
    (h.symm.trans ?_)
  rw [← WithZero.coe_mul, ← ofAdd_add]
  push_cast
  rfl

end Lattice

end TauCeti
