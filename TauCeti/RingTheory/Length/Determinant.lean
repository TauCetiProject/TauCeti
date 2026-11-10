/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Matrix.Transvection
public import Mathlib.RingTheory.OrderOfVanishing.Basic
public import TauCeti.RingTheory.Length.Endomorphism
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.RingTheory.Localization.Integer
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

/-- The cokernel of an endomorphism of a module with a finite basis is the cokernel of its
matrix. -/
theorem _root_.Module.Basis.length_quotient_range_eq_length_quotient_range_toMatrix
    {R ι F : Type*} [CommRing R] [Fintype ι] [DecidableEq ι] [AddCommGroup F] [Module R F]
    (b : Module.Basis ι R F) (ψ : F →ₗ[R] F) :
    Module.length R (F ⧸ LinearMap.range ψ) =
      Module.length R ((ι → R) ⧸ LinearMap.range (LinearMap.toMatrix b b ψ).mulVecLin) := by
  refine (Submodule.Quotient.equiv _ _ b.equivFun ?_).length_eq
  ext x
  simp only [Submodule.mem_map, LinearMap.mem_range, LinearEquiv.coe_coe, mulVecLin_apply]
  constructor
  · rintro ⟨_, ⟨y, rfl⟩, rfl⟩
    exact ⟨b.equivFun y, by
      rw [Module.Basis.equivFun_apply, Module.Basis.equivFun_apply, LinearMap.toMatrix_mulVec_repr]⟩
  · rintro ⟨y, rfl⟩
    refine ⟨ψ (b.equivFun.symm y), ⟨_, rfl⟩, ?_⟩
    conv_rhs => rw [← b.equivFun.apply_symm_apply y]
    rw [Module.Basis.equivFun_apply, Module.Basis.equivFun_apply, LinearMap.toMatrix_mulVec_repr]

variable {A ι : Type*} [CommRing A] [IsDomain A] [Fintype ι] [DecidableEq ι]

/-- **Rigidity of additive functions of nonsingular matrices.** Over a domain `A`, a function `g`
on square matrices with `g (M * N) = g M + g N` for nonsingular `M` and `N`, vanishing on
nonsingular diagonal matrices and on transvections, vanishes on every nonsingular matrix. -/
theorem _root_.Matrix.eq_zero_of_map_mul_of_diagonal_of_transvection {G : Type*}
    [AddZeroClass G] (g : Matrix ι ι A → G)
    (hmul : ∀ M N : Matrix ι ι A, M.det ≠ 0 → N.det ≠ 0 → g (M * N) = g M + g N)
    (hdiag : ∀ d : ι → A, (∀ i, d i ≠ 0) → g (diagonal d) = 0)
    (htransvec : ∀ i j : ι, i ≠ j → ∀ x : A, g (transvection i j x) = 0)
    {M : Matrix ι ι A} (hM : M.det ≠ 0) : g M = 0 := by
  classical
  let K := FractionRing A
  let φ : Matrix ι ι A →+* Matrix ι ι K := (algebraMap A K).mapMatrix
  have hφ : ∀ M : Matrix ι ι A, φ M = M.map (algebraMap A K) := fun _ ↦ rfl
  have hinj : Function.Injective φ := Matrix.map_injective (IsFractionRing.injective A K)
  have hdet : ∀ M : Matrix ι ι A, (φ M).det = algebraMap A K M.det := fun M ↦
    ((algebraMap A K).map_det M).symm
  have hsmul : ∀ (s : A) (M : Matrix ι ι A), φ (s • M) = algebraMap A K s • φ M := fun s M ↦ by
    ext; simp [hφ]
  -- Multiplying by a nonzero scalar does not change `g`.
  have hscal : ∀ (s : A) (M : Matrix ι ι A), s ≠ 0 → M.det ≠ 0 → g (s • M) = g M := by
    intro s M hs hM
    rw [smul_eq_diagonal_mul, hmul _ _ (by simp [det_diagonal, hs]) hM,
      hdiag _ fun _ ↦ hs, zero_add]
  -- An integral multiple of a nonsingular matrix over `K` is nonsingular.
  have hrep_det : ∀ (N : Matrix ι ι K) (s : A) (M : Matrix ι ι A), s ≠ 0 → N.det ≠ 0 →
      φ M = algebraMap A K s • N → M.det ≠ 0 := by
    intro N s M hs hN hM h0
    have := congrArg det hM
    rw [hdet, h0, map_zero, det_smul] at this
    exact mul_ne_zero (pow_ne_zero _ ((map_ne_zero_iff _ (IsFractionRing.injective A K)).2 hs))
      hN this.symm
  -- Two integral multiples of the same nonsingular matrix have the same value.
  have hrep_eq : ∀ (N : Matrix ι ι K) (s t : A) (M M' : Matrix ι ι A), s ≠ 0 → t ≠ 0 →
      N.det ≠ 0 → φ M = algebraMap A K s • N → φ M' = algebraMap A K t • N → g M = g M' := by
    intro N s t M M' hs ht hN hM hM'
    have h : t • M = s • M' := hinj (by rw [hsmul, hsmul, hM, hM', smul_smul, smul_smul, mul_comm])
    rw [← hscal t M ht (hrep_det N s M hs hN hM), h, hscal s M' hs (hrep_det N t M' ht hN hM')]
  -- Every matrix over `K` has an integral multiple.
  have hrep : ∀ N : Matrix ι ι K, ∃ s : A, s ≠ 0 ∧ ∃ M : Matrix ι ι A,
      φ M = algebraMap A K s • N := by
    intro N
    obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors A)
      fun p : ι × ι ↦ N p.1 p.2
    choose M hM using hb
    refine ⟨b, nonZeroDivisors.coe_ne_zero b, of fun i j ↦ M (i, j), ?_⟩
    ext i j
    rw [hφ, map_apply, of_apply, hM]
    exact Algebra.smul_def _ _
  -- The matrices over `K` on all of whose integral multiples `g` vanishes.
  let Good (N : Matrix ι ι K) : Prop :=
    ∀ (s : A) (M : Matrix ι ι A), s ≠ 0 → φ M = algebraMap A K s • N → g M = 0
  have hgood_mul : ∀ N N' : Matrix ι ι K, N.det ≠ 0 → N'.det ≠ 0 → Good N → Good N' →
      Good (N * N') := by
    intro N N' hN hN' hgN hgN' s M hs hM
    obtain ⟨s₁, hs₁, M₁, hM₁⟩ := hrep N
    obtain ⟨s₂, hs₂, M₂, hM₂⟩ := hrep N'
    have hM₁₂ : φ (M₁ * M₂) = algebraMap A K (s₁ * s₂) • (N * N') := by
      rw [map_mul, hM₁, hM₂, smul_mul_smul_comm, map_mul]
    rw [hrep_eq _ s (s₁ * s₂) M (M₁ * M₂) hs (mul_ne_zero hs₁ hs₂)
      (by rw [det_mul]; exact mul_ne_zero hN hN') hM hM₁₂,
      hmul _ _ (hrep_det N s₁ M₁ hs₁ hN hM₁) (hrep_det N' s₂ M₂ hs₂ hN' hM₂),
      hgN s₁ M₁ hs₁ hM₁, hgN' s₂ M₂ hs₂ hM₂, add_zero]
  have hgood_diag : ∀ D : ι → K, (∀ i, D i ≠ 0) → Good (diagonal D) := by
    intro D hD s M hs hM
    have hentry : ∀ i j, algebraMap A K (M i j) = algebraMap A K s * diagonal D i j := fun i j ↦ by
      simpa [hφ] using congrFun (congrFun hM i) j
    have hMd : M = diagonal fun i ↦ M i i := by
      ext i j
      by_cases hij : i = j
      · subst hij; simp
      · refine IsFractionRing.injective A K ?_
        rw [hentry, diagonal_apply_ne _ hij, diagonal_apply_ne _ hij, mul_zero, map_zero]
    rw [hMd]
    refine hdiag _ fun i h ↦ ?_
    have := hentry i i
    rw [h, map_zero, diagonal_apply_eq] at this
    exact mul_ne_zero ((map_ne_zero_iff _ (IsFractionRing.injective A K)).2 hs) (hD i) this.symm
  have hgood_transvec : ∀ (i j : ι), i ≠ j → ∀ c : K, Good (transvection i j c) := by
    intro i j hij c s M hs hM
    obtain ⟨x, t, ht, rfl⟩ := IsFractionRing.div_surjective (A := A) c
    have ht0 : t ≠ 0 := nonZeroDivisors.ne_zero ht
    have htK : algebraMap A K t ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective A K)).2 ht0
    -- The transvection with entry `x / t` is `t⁻¹ • u * T x * v`, for the diagonal `u` and `v`.
    let u : ι → A := Function.update 1 j t
    let v : ι → A := Function.update (fun _ ↦ t) j 1
    have hu : ∀ k, u k ≠ 0 := fun k ↦ by
      by_cases hk : k = j <;> simp [u, hk, ht0]
    have hv : ∀ k, v k ≠ 0 := fun k ↦ by
      by_cases hk : k = j <;> simp [v, hk, ht0]
    have hM₀ : φ (diagonal u * transvection i j x * diagonal v) =
        algebraMap A K t • transvection i j (algebraMap A K x / algebraMap A K t) := by
      ext a b
      simp only [hφ, map_apply, mul_diagonal, diagonal_mul,
        transvection, u, v, Function.update_apply,
        Pi.one_apply]
      by_cases hab : a = b
      · subst hab
        have : ¬(i = a ∧ j = a) := fun h ↦ hij (h.1.trans h.2.symm)
        by_cases haj : a = j <;> simp [haj, this, mul_comm, hij]
      · by_cases h : i = a ∧ j = b
        · obtain ⟨rfl, rfl⟩ := h
          simp [hab, mul_div_cancel₀ _ htK]
        · simp [hab, h]
    have hdu : (diagonal u).det ≠ 0 := by
      rw [det_diagonal]; exact Finset.prod_ne_zero_iff.2 fun k _ ↦ hu k
    have hdv : (diagonal v).det ≠ 0 := by
      rw [det_diagonal]; exact Finset.prod_ne_zero_iff.2 fun k _ ↦ hv k
    have hT : (transvection i j x).det ≠ 0 := by
      rw [det_transvection_of_ne _ _ hij]; exact one_ne_zero
    have hTK : (transvection i j (algebraMap A K x / algebraMap A K t)).det ≠ 0 := by
      rw [det_transvection_of_ne _ _ hij]; exact one_ne_zero
    rw [hrep_eq _ s t M _ hs ht0 hTK hM hM₀,
      hmul _ _ (by rw [det_mul]; exact mul_ne_zero hdu hT) hdv, hmul _ _ hdu hT,
      hdiag u hu, hdiag v hv, htransvec i j hij x, add_zero, add_zero]
  have hgood_list : ∀ L : List (TransvectionStruct ι K),
      Good (L.map TransvectionStruct.toMatrix).prod := by
    intro L
    induction L with
    | nil =>
      simpa only [List.map_nil, List.prod_nil, diagonal_one] using
        hgood_diag (fun _ ↦ (1 : K)) fun _ ↦ one_ne_zero
    | cons T L ih =>
      rw [List.map_cons, List.prod_cons]
      exact hgood_mul _ _ (by rw [TransvectionStruct.det]; exact one_ne_zero)
        (by rw [TransvectionStruct.det_toMatrix_prod]; exact one_ne_zero)
        (hgood_transvec T.i T.j T.hij T.c) ih
  -- Over `K`, the image of `M` is a product of transvections and a diagonal matrix.
  obtain ⟨L, L', D, hD⟩ := Pivot.exists_list_transvec_mul_diagonal_mul_list_transvec (φ M)
  have hφM : (φ M).det ≠ 0 := by
    rw [hdet]; exact (map_ne_zero_iff _ (IsFractionRing.injective A K)).2 hM
  have hdetD : (diagonal D).det ≠ 0 := by
    have := hφM
    rwa [hD, det_mul, det_mul, TransvectionStruct.det_toMatrix_prod,
      TransvectionStruct.det_toMatrix_prod, one_mul, mul_one] at this
  have hDi : ∀ i, D i ≠ 0 := fun i ↦ by
    rw [det_diagonal] at hdetD
    exact (Finset.prod_ne_zero_iff.1 hdetD) i (Finset.mem_univ i)
  have hgood : Good (φ M) := by
    rw [hD]
    refine hgood_mul _ _ ?_ (by rw [TransvectionStruct.det_toMatrix_prod]; exact one_ne_zero)
      (hgood_mul _ _ (by rw [TransvectionStruct.det_toMatrix_prod]; exact one_ne_zero) hdetD
        (hgood_list L) (hgood_diag D hDi)) (hgood_list L')
    rw [det_mul, TransvectionStruct.det_toMatrix_prod, one_mul]
    exact hdetD
  exact hgood 1 M one_ne_zero (by rw [map_one, one_smul])

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
`det φ` has order `n`.

A free submodule `F ≤ M` with `cM ≤ F` for some nonzero `c` is preserved by `cφ`, and its basis
is a `K`-basis of `V`. The cokernel of `cφ` on `F` is that of `cφ` on `M`, of length
`rank M * ord c + n`, and by the free case it is also the order of `det (cφ) = c ^ rank M * det φ`.
-/
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
