/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.RingTheory.Bialgebra.MonoidAlgebra
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import TauCeti.Algebra.AlgebraicGroup.AdditiveGroup.Basic
public import TauCeti.Algebra.AlgebraicGroup.AdditiveGroup.CoordinateBaseChange
public import TauCeti.Algebra.AlgebraicGroup.AdditiveGroup.LinearlyReductive
public import TauCeti.Algebra.AlgebraicGroup.AdditiveGroup.Unipotent
public import TauCeti.Algebra.AlgebraicGroup.Reductive.Basic
public import TauCeti.Algebra.AlgebraicGroup.RootsOfUnity.Basic
public import TauCeti.Algebra.Bialgebra.ComoduleAlgebra
public import TauCeti.Algebra.Coalgebra.Comodule.PointsAction
public import TauCeti.RingTheory.MvPolynomial.SAGBI.Basic
import TauCeti.RingTheory.Idempotents.Connected.Spectrum
import TauCeti.RingTheory.Spectrum.Prime.Topology

/-!
# Linear algebraic group invariant algebras with finite SAGBI bases

In characteristic zero, finite SAGBI bases for polynomial invariant algebras of linear algebraic
group actions do not characterize connected reductive groups. This file formalizes two explicit
algebraic-group coaction examples exhibiting both boundaries of any naive connected-reductive
characterization, using algebraic comodule-algebra coinvariants (`TauCeti.ComoduleAlgebra`)
rather than pointwise group actions:

1. **The disconnected group `μ₂ ≤ GL₁`** acting on `R[x]` by the sign coaction
   `x ↦ x ⊗ g` (whose point action at `-1 ∈ μ₂(R)` is `x ↦ -x`). Its coinvariant subalgebra is
   `R[x²]` over any commutative semiring `R`, with singleton SAGBI basis `{x²}` for every monomial
   order, while `Spec R[μ₂]` is disconnected whenever `2` is a unit in a nontrivial commutative
   ring `R` (in particular over `ℂ`).
2. **The connected unipotent group `𝔾ₐ ≤ GL₂`** acting on `R[x, y]` by the contragredient shear
   coaction `x ↦ x ⊗ 1`, `y ↦ y ⊗ 1 - x ⊗ t` (whose point action at `a ∈ 𝔾ₐ(R)` is
   `x ↦ x, y ↦ y - ax`). Comparing top `t`-degrees via divided-power coaction components shows
   that its coinvariant subalgebra is `R[x]` over every commutative ring `R`, with singleton SAGBI
   basis `{x}` for every monomial order, while over every field `k` (in particular `ℂ`) the group
   `𝔾ₐ` is connected, geometrically connected, smooth unipotent, not linearly reductive, and not
   reductive.

As a general preliminary, any monomial subalgebra `R[X^d : d ∈ S]` equals its own initial algebra
for every monomial order and therefore has `{X^d : d ∈ S}` as a SAGBI basis.

## Main definitions

* `TauCeti.mu2SignCoactAlgHom`, `TauCeti.mu2SignComoduleAlgebra`, `TauCeti.mu2SignCoinvariants`:
  the sign coaction of `μ₂` on `R[x]` and its coinvariant subalgebra.
* `TauCeti.gaShearCoactAlgHom`, `TauCeti.gaShearComoduleAlgebra`, `TauCeti.gaShearCoinvariants`:
  the contragredient shear coaction of `𝔾ₐ` on `R[x, y]` and its coinvariant subalgebra.

## Main results

* `MonomialOrder.initialAlgebra_adjoin_image_monomial`,
  `MonomialOrder.isSAGBIBasis_image_monomial`,
  `MonomialOrder.isSAGBIBasis_singleton_monomial`: every monomial subalgebra equals its own
  initial algebra and has its generating monomials as a SAGBI basis for every monomial order.
* `TauCeti.mu2SignCoinvariants_eq_adjoin_X_sq` and
  `TauCeti.isSAGBIBasis_singleton_X_sq_mu2SignCoinvariants`: the `μ₂`-coinvariants equal `R[x²]`
  with singleton SAGBI basis `{x²}` for every monomial order.
* `TauCeti.not_connectedSpace_primeSpectrum_mu2`: `Spec R[μ₂]` is disconnected when `2` is a unit
  in a nontrivial commutative ring `R`.
* `TauCeti.mu2SignCoinvariants_complex_boundary`: the combined `ℂ`-boundary statement for `μ₂`.
* `TauCeti.gaShearCoinvariants_eq_adjoin_X_zero` and
  `TauCeti.isSAGBIBasis_singleton_X_zero_gaShearCoinvariants`: the `𝔾ₐ`-coinvariants equal `R[x]`
  with singleton SAGBI basis `{x}` for every monomial order.
* `TauCeti.connectedSpace_primeSpectrum_ga` and `TauCeti.not_reductiveCommHopfAlgProperty_ga`:
  over any field, `𝔾ₐ` is connected and not reductive.
* `TauCeti.gaShearCoinvariants_complex_boundary`: the combined `ℂ`-boundary statement for `𝔾ₐ`.

## References

* L. Robbiano, M. Sweedler, *Subalgebra bases*, in *Commutative Algebra (Salvador, 1988)*,
  Lecture Notes in Mathematics 1430, Springer, 1990, 61–87.
* B. Sturmfels, *Gröbner Bases and Convex Polytopes*, University Lecture Series 8, AMS, 1996,
  Chapter 11.
* J. S. Milne, *Algebraic Groups* (2017), Chapters 12, 14, and 19.
-/

public section

open MvPolynomial
open scoped TensorProduct

namespace MonomialOrder

section MonomialSubalgebra

variable {σ R : Type*} [CommSemiring R]

private theorem support_subset_closure_of_mem_adjoin_monomial {S : Set (σ →₀ ℕ)}
    {f : MvPolynomial σ R}
    (hf : f ∈ Algebra.adjoin R ((fun d ↦ monomial d (1 : R)) '' S)) :
    (f.support : Set (σ →₀ ℕ)) ⊆ AddSubmonoid.closure S := by
  classical
  induction hf using Algebra.adjoin_induction with
  | mem _ hx =>
    obtain ⟨d, hd, rfl⟩ := hx
    exact (Finset.coe_subset.2 support_monomial_subset).trans (by
      simpa using AddSubmonoid.subset_closure hd)
  | algebraMap r =>
    by_cases hr : r = 0
    · simp [hr]
    · simp [MvPolynomial.algebraMap_eq, support_C, hr]
  | add x y _ _ hx hy =>
    exact (Finset.coe_subset.2 support_add).trans (by simpa using And.intro hx hy)
  | mul x y _ _ hx hy =>
    refine (Finset.coe_subset.2 (support_mul x y)).trans ?_
    rw [Finset.coe_add]
    exact Set.add_subset_iff.2 fun a ha b hb ↦ add_mem (hx ha) (hy hb)

private theorem monomial_one_mem_adjoin_of_mem_closure {S : Set (σ →₀ ℕ)} {a : σ →₀ ℕ}
    (ha : a ∈ AddSubmonoid.closure S) :
    monomial a (1 : R) ∈ Algebra.adjoin R ((fun d ↦ monomial d (1 : R)) '' S) := by
  induction ha using AddSubmonoid.closure_induction with
  | mem d hd => exact Algebra.subset_adjoin ⟨d, hd, rfl⟩
  | zero => simp
  | add x y _ _ hx hy =>
    simpa [monomial_mul_monomial] using mul_mem hx hy

/-- Every monomial subalgebra `R[X^d : d ∈ S]` equals its own initial algebra for every monomial
order `m`. -/
theorem initialAlgebra_adjoin_image_monomial (m : MonomialOrder σ) (S : Set (σ →₀ ℕ)) :
    m.initialAlgebra (Algebra.adjoin R ((fun d ↦ monomial d (1 : R)) '' S)) =
      Algebra.adjoin R ((fun d ↦ monomial d (1 : R)) '' S) := by
  rw [initialAlgebra_def]
  refine le_antisymm (Algebra.adjoin_le ?_) (Algebra.adjoin_le ?_)
  · rintro _ ⟨f, hf, rfl⟩
    rcases eq_or_ne f 0 with rfl | hf0
    · simp
    · have hdeg : m.degree f ∈ AddSubmonoid.closure S :=
        support_subset_closure_of_mem_adjoin_monomial hf (m.degree_mem_support hf0)
      have hmon : monomial (m.degree f) (1 : R) ∈
          Algebra.adjoin R ((fun d ↦ monomial d (1 : R)) '' S) :=
        monomial_one_mem_adjoin_of_mem_closure hdeg
      rw [leadingTerm, ← mul_one (m.leadingCoeff f), ← C_mul_monomial,
        ← MvPolynomial.algebraMap_eq]
      exact mul_mem (Subalgebra.algebraMap_mem _ _) hmon
  · rintro _ ⟨d, hd, rfl⟩
    dsimp only
    rw [← m.leadingTerm_monomial d (1 : R)]
    exact Algebra.subset_adjoin ⟨monomial d 1, Algebra.subset_adjoin ⟨d, hd, rfl⟩, rfl⟩

/-- The generating monomials `{X^d : d ∈ S}` form a SAGBI basis of the monomial subalgebra
`R[X^d : d ∈ S]` for every monomial order `m`. -/
theorem isSAGBIBasis_image_monomial (m : MonomialOrder σ) (S : Set (σ →₀ ℕ)) :
    m.IsSAGBIBasis ((fun d ↦ monomial d (1 : R)) '' S)
      (Algebra.adjoin R ((fun d ↦ monomial d (1 : R)) '' S)) := by
  refine isSAGBIBasis_iff.2 ⟨Algebra.subset_adjoin, ?_⟩
  rw [m.initialAlgebra_adjoin_image_monomial (R := R) S]
  congr 1
  ext p
  constructor
  · rintro ⟨_, ⟨d, hd, rfl⟩, rfl⟩
    exact ⟨d, hd, (m.leadingTerm_monomial d (1 : R)).symm⟩
  · rintro ⟨d, hd, rfl⟩
    exact ⟨monomial d 1, ⟨d, hd, rfl⟩, m.leadingTerm_monomial d (1 : R)⟩

/-- A single monomial `{X^d}` is a SAGBI basis of the subalgebra `R[X^d]` it generates, for every
monomial order `m`. -/
theorem isSAGBIBasis_singleton_monomial (m : MonomialOrder σ) (d : σ →₀ ℕ) :
    m.IsSAGBIBasis {monomial d (1 : R)} (Algebra.adjoin R {monomial d (1 : R)}) := by
  simpa using m.isSAGBIBasis_image_monomial (R := R) {d}

end MonomialSubalgebra

end MonomialOrder

namespace TauCeti

open CategoryTheory WithConv

section Helper

/-- Construct a `ComoduleAlgebra` structure on `MvPolynomial σ R` from an `R`-algebra map
`ρ : MvPolynomial σ R →ₐ[R] MvPolynomial σ R ⊗[R] H` by checking coassociativity and the counit
axiom on the polynomial generators `X i`. -/
@[implicit_reducible]
private noncomputable def comoduleAlgebraOfMvPolynomialAlgHom
    {R H σ : Type*} [CommSemiring R] [CommSemiring H] [Bialgebra R H]
    (ρ : MvPolynomial σ R →ₐ[R] MvPolynomial σ R ⊗[R] H)
    (hcoassoc : ∀ i,
      (Algebra.TensorProduct.assoc R R R (MvPolynomial σ R) H H).toAlgHom
          ((Algebra.TensorProduct.map ρ (AlgHom.id R H)) (ρ (X i))) =
        (Algebra.TensorProduct.map (AlgHom.id R (MvPolynomial σ R))
          (Bialgebra.comulAlgHom R H)) (ρ (X i)))
    (hcounit : ∀ i,
      (Algebra.TensorProduct.map (AlgHom.id R (MvPolynomial σ R))
          (Bialgebra.counitAlgHom R H)) (ρ (X i)) = X i ⊗ₜ[R] (1 : R)) :
    ComoduleAlgebra R H (MvPolynomial σ R) where
  coact := ρ.toLinearMap
  coassoc := by
    have h :
        ((Algebra.TensorProduct.assoc R R R (MvPolynomial σ R) H H).toAlgHom.comp
          ((Algebra.TensorProduct.map ρ (AlgHom.id R H)).comp ρ)) =
        (Algebra.TensorProduct.map (AlgHom.id R (MvPolynomial σ R))
          (Bialgebra.comulAlgHom R H)).comp ρ :=
      MvPolynomial.algHom_ext hcoassoc
    refine LinearMap.ext fun p ↦ ?_
    exact DFunLike.congr_fun h p
  lTensor_counit_comp_coact := by
    have h :
        (Algebra.TensorProduct.map (AlgHom.id R (MvPolynomial σ R))
          (Bialgebra.counitAlgHom R H)).comp ρ =
        Algebra.TensorProduct.includeLeft :=
      MvPolynomial.algHom_ext hcounit
    refine LinearMap.ext fun p ↦ ?_
    exact DFunLike.congr_fun h p
  coact_one := map_one ρ
  coact_mul := map_mul ρ

end Helper

/-! ### Disconnected example: `μ₂ ≤ GL₁` acting on `R[x]` -/

section Mu2Sign

private lemma generator_two_ne_one : RootsOfUnityGroup.generator 2 ≠ 1 := by
  intro h
  have h0 : (1 : ZMod 2) = 0 := by
    simpa [RootsOfUnityGroup.generator] using congrArg Multiplicative.toAdd h
  exact one_ne_zero h0

private lemma generator_two_pow_odd {n : ℕ} (hn : ¬ Even n) :
    RootsOfUnityGroup.generator 2 ^ n = RootsOfUnityGroup.generator 2 := by
  obtain ⟨k, rfl⟩ := Nat.not_even_iff_odd.mp hn
  rw [pow_add, pow_mul, RootsOfUnityGroup.generator_pow_eq_one 2, one_pow, one_mul, pow_one]

section Semiring

variable (R : Type*) [CommSemiring R]

/-- The sign coaction `x ↦ x ⊗ g` of the coordinate Hopf algebra `R[μ₂]` on `R[x]`, as an
`R`-algebra homomorphism. -/
noncomputable def mu2SignCoactAlgHom :
    MvPolynomial (Fin 1) R →ₐ[R]
      MvPolynomial (Fin 1) R ⊗[R] MonoidAlgebra R (Multiplicative (ZMod 2)) :=
  MvPolynomial.aeval fun _ ↦
    X (0 : Fin 1) ⊗ₜ[R] MonoidAlgebra.single (RootsOfUnityGroup.generator 2) (1 : R)

@[simp]
theorem mu2SignCoactAlgHom_X (i : Fin 1) :
    mu2SignCoactAlgHom R (X i) =
      X (0 : Fin 1) ⊗ₜ[R] MonoidAlgebra.single (RootsOfUnityGroup.generator 2) (1 : R) := by
  simp [mu2SignCoactAlgHom]

/-- The sign comodule-algebra structure of `μ₂` on `R[x]`, sending `x ↦ x ⊗ g`.

This is not a global instance; select it explicitly or as a local instance. -/
@[implicit_reducible]
noncomputable def mu2SignComoduleAlgebra :
    ComoduleAlgebra R (MonoidAlgebra R (Multiplicative (ZMod 2))) (MvPolynomial (Fin 1) R) :=
  comoduleAlgebraOfMvPolynomialAlgHom (mu2SignCoactAlgHom R)
    (fun i ↦ by
      fin_cases i
      simp [mu2SignCoactAlgHom])
    (fun i ↦ by
      fin_cases i
      simp [mu2SignCoactAlgHom])

attribute [local instance] mu2SignComoduleAlgebra

@[simp]
theorem mu2SignComoduleAlgebra_coact_X_zero :
    Comodule.coact (R := R) (C := MonoidAlgebra R (Multiplicative (ZMod 2)))
        (X (0 : Fin 1) : MvPolynomial (Fin 1) R) =
      X (0 : Fin 1) ⊗ₜ[R] MonoidAlgebra.single (RootsOfUnityGroup.generator 2) (1 : R) := by
  change mu2SignCoactAlgHom R (X 0) = _
  simp

theorem mu2SignComoduleAlgebra_coact_monomial (d : Fin 1 →₀ ℕ) (c : R) :
    Comodule.coact (R := R) (C := MonoidAlgebra R (Multiplicative (ZMod 2)))
        (monomial d c : MvPolynomial (Fin 1) R) =
      monomial d c ⊗ₜ[R]
        MonoidAlgebra.single (RootsOfUnityGroup.generator 2 ^ d 0) (1 : R) := by
  change mu2SignCoactAlgHom R (monomial d c) = _
  have hd : d = Finsupp.single 0 (d 0) := by
    refine Finsupp.ext fun i ↦ ?_
    fin_cases i
    simp
  conv_lhs => rw [hd, ← C_mul_X_pow_eq_monomial]
  rw [map_mul, map_pow, mu2SignCoactAlgHom_X, ← MvPolynomial.algebraMap_eq, AlgHom.commutes,
    Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_pow,
    Algebra.TensorProduct.tmul_mul_tmul, one_mul, MonoidAlgebra.single_pow, one_pow,
    MvPolynomial.algebraMap_eq, C_mul_X_pow_eq_monomial, ← hd]

/-- The coinvariant subalgebra of `R[x]` under the sign coaction of `μ₂`. -/
noncomputable def mu2SignCoinvariants : Subalgebra R (MvPolynomial (Fin 1) R) :=
  ComoduleAlgebra.coinvariants R (MonoidAlgebra R (Multiplicative (ZMod 2)))
    (MvPolynomial (Fin 1) R)

theorem mu2SignCoinvariants_def :
    mu2SignCoinvariants R =
      ComoduleAlgebra.coinvariants R (MonoidAlgebra R (Multiplicative (ZMod 2)))
        (MvPolynomial (Fin 1) R) := by
  rw [mu2SignCoinvariants]

variable {R} in
@[simp]
theorem mem_mu2SignCoinvariants {p : MvPolynomial (Fin 1) R} :
    p ∈ mu2SignCoinvariants R ↔
      Comodule.coact (R := R) (C := MonoidAlgebra R (Multiplicative (ZMod 2))) p =
        p ⊗ₜ[R] (1 : MonoidAlgebra R (Multiplicative (ZMod 2))) :=
  ComoduleAlgebra.mem_coinvariants

/-- **The `μ₂`-coinvariant subalgebra of `R[x]` is `R[x²]`**, over any commutative semiring `R`. -/
theorem mu2SignCoinvariants_eq_adjoin_X_sq :
    mu2SignCoinvariants R = Algebra.adjoin R {X (0 : Fin 1) ^ 2} := by
  classical
  refine le_antisymm ?_ (Algebra.adjoin_le ?_)
  · intro p hp
    have hcoact :
        Comodule.coact (R := R) (C := MonoidAlgebra R (Multiplicative (ZMod 2))) p =
          p ⊗ₜ[R] (1 : MonoidAlgebra R (Multiplicative (ZMod 2))) :=
      mem_mu2SignCoinvariants.mp hp
    let φ : MonoidAlgebra R (Multiplicative (ZMod 2)) →ₗ[R] R :=
      (Finsupp.lapply (RootsOfUnityGroup.generator 2)).comp
        (MonoidAlgebra.coeffLinearEquiv R).toLinearMap
    have hcomp := congrArg (_root_.LinearMap.tensorComponent (R := R) φ) hcoact
    have hrhs :
        _root_.LinearMap.tensorComponent (R := R) φ
          (p ⊗ₜ[R] (1 : MonoidAlgebra R (Multiplicative (ZMod 2)))) = 0 := by
      rw [_root_.LinearMap.tensorComponent_tmul]
      have hφ1 : φ (1 : MonoidAlgebra R (Multiplicative (ZMod 2))) = 0 := by
        simp [φ, MonoidAlgebra.one_def, MonoidAlgebra.coeff_single]
      rw [hφ1, zero_smul]
    rw [hrhs] at hcomp
    have heven : ∀ d ∈ p.support, Even (d 0) := by
      intro d hd
      by_contra hodd
      have hsum :
          _root_.LinearMap.tensorComponent (R := R) φ
              (Comodule.coact (R := R) (C := MonoidAlgebra R (Multiplicative (ZMod 2))) p) =
            ∑ e ∈ p.support,
              φ (MonoidAlgebra.single (RootsOfUnityGroup.generator 2 ^ e 0) (1 : R)) •
                monomial e (p.coeff e) := by
        conv_lhs => rw [p.as_sum]
        simp only [map_sum, mu2SignComoduleAlgebra_coact_monomial,
          _root_.LinearMap.tensorComponent_tmul]
      rw [hsum] at hcomp
      have hcoeff := congrArg (fun q : MvPolynomial (Fin 1) R ↦ q.coeff d) hcomp
      simp only [AddMonoidAlgebra.coeff_zero, coeff_sum, coeff_smul, coeff_monomial,
        smul_eq_mul] at hcoeff
      rw [Finset.sum_eq_single d] at hcoeff
      · have hφd :
            φ (MonoidAlgebra.single (RootsOfUnityGroup.generator 2 ^ d 0) (1 : R)) = 1 := by
          simp [φ, generator_two_pow_odd hodd, MonoidAlgebra.coeff_single]
        simp only [↓reduceIte, hφd, one_mul] at hcoeff
        exact (mem_support_iff.mp hd) hcoeff
      · intro e _ hed
        simp [hed]
      · intro hnd
        exact (hnd hd).elim
    rw [p.as_sum]
    refine Subalgebra.sum_mem _ fun d hd ↦ ?_
    obtain ⟨k, hk⟩ := heven d hd
    have hmon : monomial d (p.coeff d) = C (p.coeff d) * (X (0 : Fin 1) ^ 2) ^ k := by
      have hd' : d = Finsupp.single 0 (2 * k) := by
        refine Finsupp.ext fun i ↦ ?_
        fin_cases i
        simpa [two_mul] using hk
      rw [hd', ← C_mul_X_pow_eq_monomial, pow_mul]
    rw [hmon, ← MvPolynomial.algebraMap_eq]
    exact mul_mem (Subalgebra.algebraMap_mem _ _)
      (pow_mem (Algebra.subset_adjoin (Set.mem_singleton _)) k)
  · rintro _ rfl
    rw [SetLike.mem_coe, mem_mu2SignCoinvariants]
    change mu2SignCoactAlgHom R (X (0 : Fin 1) ^ 2) = _
    rw [map_pow, mu2SignCoactAlgHom_X, Algebra.TensorProduct.tmul_pow,
      RootsOfUnityGroup.single_generator_pow_eq_one 2]

/-- The singleton `{x²}` is a SAGBI basis of the `μ₂`-coinvariant subalgebra for every monomial
order on `Fin 1`. -/
theorem isSAGBIBasis_singleton_X_sq_mu2SignCoinvariants (m : MonomialOrder (Fin 1)) :
    m.IsSAGBIBasis {X (0 : Fin 1) ^ 2} (mu2SignCoinvariants R) := by
  rw [mu2SignCoinvariants_eq_adjoin_X_sq, X_pow_eq_monomial]
  exact m.isSAGBIBasis_singleton_monomial (Finsupp.single 0 2)

end Semiring

section Ring

variable (R : Type*) [CommRing R]

attribute [local instance] mu2SignComoduleAlgebra

/-- Evaluating the `μ₂`-sign coaction at the `R`-point `-1 ∈ μ₂(R)` yields the sign involution
`x ↦ -x`. -/
theorem mu2SignComoduleAlgebra_endOfPoint_negOne_X_zero :
    Comodule.endOfPoint (R := R) (H := MonoidAlgebra R (Multiplicative (ZMod 2)))
      (MvPolynomial (Fin 1) R)
      ((RootsOfUnityGroup.pointsMulEquiv (R := R) (A := R) 2).symm
        ⟨-1, by simp [mem_rootsOfUnity]⟩).ofConv
      ((1 : R) ⊗ₜ[R] X (0 : Fin 1)) =
    (1 : R) ⊗ₜ[R] (-X (0 : Fin 1)) := by
  rw [Comodule.endOfPoint_tmul, mu2SignComoduleAlgebra_coact_X_zero, one_smul]
  simp only [LinearMap.lTensor_tmul, AlgHom.toLinearMap_apply,
    RootsOfUnityGroup.pointsMulEquiv_symm_apply_single_generator,
    TensorProduct.comm_tmul]
  change (-1 : R) ⊗ₜ[R] X (0 : Fin 1) = (1 : R) ⊗ₜ[R] (-X (0 : Fin 1))
  simp [TensorProduct.neg_tmul, TensorProduct.tmul_neg]

/-- **The group scheme `μ₂` is disconnected** whenever `2` is a unit in a nontrivial commutative
ring `R`: `(1 + g) / 2` is a nontrivial idempotent in `R[μ₂]`. -/
theorem not_connectedSpace_primeSpectrum_mu2 {R : Type*} [CommRing R] [Nontrivial R]
    (h2 : IsUnit (2 : R)) :
    ¬ ConnectedSpace (PrimeSpectrum (MonoidAlgebra R (Multiplicative (ZMod 2)))) := by
  intro hconn
  let t : MonoidAlgebra R (Multiplicative (ZMod 2)) :=
    MonoidAlgebra.single (RootsOfUnityGroup.generator 2) (1 : R)
  let uinv : R := ((h2.unit⁻¹ : Rˣ) : R)
  let e : MonoidAlgebra R (Multiplicative (ZMod 2)) := uinv • (1 + t)
  have ht2 : t * t = 1 := by
    rw [← sq]
    exact RootsOfUnityGroup.single_generator_pow_eq_one (R := R) 2
  have h1t : (1 + t) * (1 + t) = (2 : R) • (1 + t) := by
    calc
      (1 + t) * (1 + t) = 1 + t + t + t * t := by ring
      _ = 1 + t + t + 1 := by rw [ht2]
      _ = (1 + t) + (1 + t) := by abel
      _ = (2 : R) • (1 + t) := by rw [two_smul]
  have huinv_mul : uinv * (2 : R) = 1 := by
    have hu : (h2.unit : R) = 2 := h2.unit_spec
    rw [← hu]
    exact h2.unit.inv_mul
  have huinv_ne : uinv ≠ 0 := Units.ne_zero (h2.unit⁻¹)
  have he : IsIdempotentElem e := by
    rw [IsIdempotentElem]
    change (uinv • (1 + t)) * (uinv • (1 + t)) = uinv • (1 + t)
    rw [smul_mul_smul_comm, h1t, smul_smul, mul_assoc, huinv_mul, mul_one]
  rcases he.eq_zero_or_eq_one_of_preconnectedSpace with h0 | h1
  · have hc := congrArg (fun x : MonoidAlgebra R (Multiplicative (ZMod 2)) ↦ x.coeff 1) h0
    exact huinv_ne (by simpa [e, t, MonoidAlgebra.one_def, MonoidAlgebra.coeff_single] using hc)
  · have hc := congrArg
      (fun x : MonoidAlgebra R (Multiplicative (ZMod 2)) ↦
        x.coeff (RootsOfUnityGroup.generator 2)) h1
    exact huinv_ne (by simpa [e, t, MonoidAlgebra.one_def, MonoidAlgebra.coeff_single] using hc)

/-- **Disconnected boundary example over `ℂ`:** the disconnected group `μ₂ ≤ GL₁` acting on
`ℂ[x]` has coinvariant subalgebra `ℂ[x²]` with singleton SAGBI basis `{x²}` for every monomial
order. -/
theorem mu2SignCoinvariants_complex_boundary :
    mu2SignCoinvariants ℂ = Algebra.adjoin ℂ {X (0 : Fin 1) ^ 2} ∧
    (∀ m : MonomialOrder (Fin 1),
      m.IsSAGBIBasis {X (0 : Fin 1) ^ 2} (mu2SignCoinvariants ℂ)) ∧
    ¬ ConnectedSpace (PrimeSpectrum (MonoidAlgebra ℂ (Multiplicative (ZMod 2)))) :=
  ⟨mu2SignCoinvariants_eq_adjoin_X_sq ℂ,
    isSAGBIBasis_singleton_X_sq_mu2SignCoinvariants ℂ,
    not_connectedSpace_primeSpectrum_mu2 (by norm_num)⟩

end Ring

end Mu2Sign

/-! ### Connected non-reductive unipotent example: `𝔾ₐ ≤ GL₂` acting on `R[x, y]` -/

section GaShear

section CommRing

variable (R : Type*) [CommRing R]

/-- The contragredient shear coaction `x ↦ x ⊗ 1`, `y ↦ y ⊗ 1 - x ⊗ t` of the coordinate Hopf
algebra `R[t] = SymmetricAlgebra R R` of `𝔾ₐ` on `R[x, y]`, as an `R`-algebra homomorphism. -/
noncomputable def gaShearCoactAlgHom :
    MvPolynomial (Fin 2) R →ₐ[R] MvPolynomial (Fin 2) R ⊗[R] SymmetricAlgebra R R :=
  MvPolynomial.aeval
    ![X (0 : Fin 2) ⊗ₜ[R] (1 : SymmetricAlgebra R R),
      X (1 : Fin 2) ⊗ₜ[R] (1 : SymmetricAlgebra R R) -
        X (0 : Fin 2) ⊗ₜ[R] SymmetricAlgebra.ι R R 1]

@[simp]
theorem gaShearCoactAlgHom_X_zero :
    gaShearCoactAlgHom R (X (0 : Fin 2)) =
      X (0 : Fin 2) ⊗ₜ[R] (1 : SymmetricAlgebra R R) := by
  simp [gaShearCoactAlgHom]

@[simp]
theorem gaShearCoactAlgHom_X_one :
    gaShearCoactAlgHom R (X (1 : Fin 2)) =
      X (1 : Fin 2) ⊗ₜ[R] (1 : SymmetricAlgebra R R) -
        X (0 : Fin 2) ⊗ₜ[R] SymmetricAlgebra.ι R R 1 := by
  simp [gaShearCoactAlgHom]

/-- The contragredient shear comodule-algebra structure of `𝔾ₐ` on `R[x, y]`, sending
`x ↦ x ⊗ 1` and `y ↦ y ⊗ 1 - x ⊗ t`.

This is not a global instance; select it explicitly or as a local instance. -/
@[implicit_reducible]
noncomputable def gaShearComoduleAlgebra :
    ComoduleAlgebra R (SymmetricAlgebra R R) (MvPolynomial (Fin 2) R) :=
  comoduleAlgebraOfMvPolynomialAlgHom (gaShearCoactAlgHom R)
    (fun i ↦ by
      fin_cases i
      · simp [gaShearCoactAlgHom, Algebra.TensorProduct.one_def]
      · simp [gaShearCoactAlgHom, Algebra.TensorProduct.one_def, SymmetricAlgebra.comul_ι,
          TensorProduct.tmul_add, TensorProduct.sub_tmul, sub_sub])
    (fun i ↦ by
      fin_cases i
      · simp [gaShearCoactAlgHom]
      · simp [gaShearCoactAlgHom, SymmetricAlgebra.algebraMapInv_ι])

attribute [local instance] gaShearComoduleAlgebra

@[simp]
theorem gaShearComoduleAlgebra_coact_X_zero :
    Comodule.coact (R := R) (C := SymmetricAlgebra R R)
        (X (0 : Fin 2) : MvPolynomial (Fin 2) R) =
      X (0 : Fin 2) ⊗ₜ[R] (1 : SymmetricAlgebra R R) := by
  change gaShearCoactAlgHom R (X 0) = _
  simp

@[simp]
theorem gaShearComoduleAlgebra_coact_X_one :
    Comodule.coact (R := R) (C := SymmetricAlgebra R R)
        (X (1 : Fin 2) : MvPolynomial (Fin 2) R) =
      X (1 : Fin 2) ⊗ₜ[R] (1 : SymmetricAlgebra R R) -
        X (0 : Fin 2) ⊗ₜ[R] SymmetricAlgebra.ι R R 1 := by
  change gaShearCoactAlgHom R (X 1) = _
  simp

/-- Evaluating the `𝔾ₐ`-shear coaction at `a ∈ 𝔾ₐ(R)` fixes `x`. -/
theorem gaShearComoduleAlgebra_endOfPoint_X_zero (a : R) :
    Comodule.endOfPoint (R := R) (H := SymmetricAlgebra R R) (MvPolynomial (Fin 2) R)
      ((AdditiveGroup.gaPointsMulEquiv (R := R) (A := R)).symm (Multiplicative.ofAdd a)).ofConv
      ((1 : R) ⊗ₜ[R] X (0 : Fin 2)) =
    (1 : R) ⊗ₜ[R] X (0 : Fin 2) :=
  Comodule.endOfPoint_tmul_of_coact_eq_tmul_one
    (gaShearComoduleAlgebra_coact_X_zero R) _ 1

/-- Evaluating the `𝔾ₐ`-shear coaction at `a ∈ 𝔾ₐ(R)` sends `y ↦ y - a x`. -/
theorem gaShearComoduleAlgebra_endOfPoint_X_one (a : R) :
    Comodule.endOfPoint (R := R) (H := SymmetricAlgebra R R) (MvPolynomial (Fin 2) R)
      ((AdditiveGroup.gaPointsMulEquiv (R := R) (A := R)).symm (Multiplicative.ofAdd a)).ofConv
      ((1 : R) ⊗ₜ[R] X (1 : Fin 2)) =
    (1 : R) ⊗ₜ[R] (X (1 : Fin 2) - C a * X (0 : Fin 2)) := by
  rw [Comodule.endOfPoint_tmul, gaShearComoduleAlgebra_coact_X_one, one_smul]
  simp only [map_sub, LinearMap.lTensor_tmul, AlgHom.toLinearMap_apply, map_one,
    AdditiveGroup.gaPointsMulEquiv_symm_apply_ι, toAdd_ofAdd, TensorProduct.comm_tmul]
  rw [TensorProduct.tmul_sub]
  congr 1
  rw [← MvPolynomial.smul_eq_C_mul, ← TensorProduct.smul_tmul, smul_eq_mul, mul_one]

/-- The coinvariant subalgebra of `R[x, y]` under the contragredient shear coaction of `𝔾ₐ`. -/
noncomputable def gaShearCoinvariants : Subalgebra R (MvPolynomial (Fin 2) R) :=
  ComoduleAlgebra.coinvariants R (SymmetricAlgebra R R) (MvPolynomial (Fin 2) R)

theorem gaShearCoinvariants_def :
    gaShearCoinvariants R =
      ComoduleAlgebra.coinvariants R (SymmetricAlgebra R R) (MvPolynomial (Fin 2) R) := by
  rw [gaShearCoinvariants]

variable {R} in
@[simp]
theorem mem_gaShearCoinvariants {p : MvPolynomial (Fin 2) R} :
    p ∈ gaShearCoinvariants R ↔
      Comodule.coact (R := R) (C := SymmetricAlgebra R R) p =
        p ⊗ₜ[R] (1 : SymmetricAlgebra R R) :=
  ComoduleAlgebra.mem_coinvariants

private theorem gaShear_coact_monomial (e : Fin 2 →₀ ℕ) (c : R) :
    Comodule.coact (R := R) (C := SymmetricAlgebra R R)
        (monomial e c : MvPolynomial (Fin 2) R) =
      ∑ k ∈ Finset.range (e 1 + 1),
        monomial (Finsupp.single 0 (e 0 + k) + Finsupp.single 1 (e 1 - k))
          (c * (-1 : R) ^ k * ((e 1).choose k : R)) ⊗ₜ[R]
            ((SymmetricAlgebra.ι R R 1 : SymmetricAlgebra R R) ^ k) := by
  change gaShearCoactAlgHom R (monomial e c) = _
  have he : e = Finsupp.single 0 (e 0) + Finsupp.single 1 (e 1) := by
    refine Finsupp.ext fun i ↦ ?_
    fin_cases i <;> simp
  have hmon : monomial e c = C c * X (0 : Fin 2) ^ e 0 * X (1 : Fin 2) ^ e 1 := by
    conv_lhs => rw [he]
    rw [C_mul_X_pow_eq_monomial, X_pow_eq_monomial, monomial_mul_monomial, mul_one]
  rw [hmon, map_mul, map_mul, map_pow, map_pow, ← MvPolynomial.algebraMap_eq, AlgHom.commutes,
    Algebra.TensorProduct.algebraMap_apply, gaShearCoactAlgHom_X_zero, gaShearCoactAlgHom_X_one,
    Algebra.TensorProduct.tmul_pow, one_pow, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
    sub_eq_add_neg, add_comm, add_pow, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  have hneg :
      (-(X (0 : Fin 2) ⊗ₜ[R] SymmetricAlgebra.ι R R 1)) ^ k =
        ((-1 : MvPolynomial (Fin 2) R) ^ k * X (0 : Fin 2) ^ k) ⊗ₜ[R]
          ((SymmetricAlgebra.ι R R 1 : SymmetricAlgebra R R) ^ k) := by
    rw [show -(X (0 : Fin 2) ⊗ₜ[R] SymmetricAlgebra.ι R R 1) =
        (-X (0 : Fin 2)) ⊗ₜ[R] SymmetricAlgebra.ι R R 1 by simp [TensorProduct.neg_tmul],
      Algebra.TensorProduct.tmul_pow, neg_eq_neg_one_mul, mul_pow]
  rw [hneg, Algebra.TensorProduct.tmul_pow, one_pow, Algebra.TensorProduct.tmul_mul_tmul,
    mul_one, ← nsmul_eq_mul', ← Nat.cast_smul_eq_nsmul R, TensorProduct.smul_tmul',
    Algebra.TensorProduct.tmul_mul_tmul, one_mul, MvPolynomial.algebraMap_eq]
  congr 1
  rw [← mul_one (c * (-1 : R) ^ k * ((e 1).choose k : R)), ← monomial_mul_monomial,
    ← C_mul_X_pow_eq_monomial, ← X_pow_eq_monomial, MvPolynomial.smul_eq_C_mul, map_mul, map_mul,
    map_pow, map_neg, C_1, pow_add]
  ring

private theorem gaShear_coactComponent_monomial_of_lt {e : Fin 2 →₀ ℕ} {c : R} {d : ℕ}
    (h : e 1 < d) :
    AdditiveGroup.coactComponent R (MvPolynomial (Fin 2) R) d (monomial e c) = 0 := by
  rw [AdditiveGroup.coactComponent_apply, gaShear_coact_monomial, map_sum]
  refine Finset.sum_eq_zero fun k hk ↦ ?_
  have hkd : k ≠ d := by
    have := Finset.mem_range.mp hk
    omega
  rw [_root_.LinearMap.tensorComponent_tmul, AdditiveGroup.coeff_pow, ite_eq_right hkd, zero_smul]

private theorem gaShear_coactComponent_monomial_of_eq {e : Fin 2 →₀ ℕ} {c : R} {d : ℕ}
    (h : e 1 = d) :
    AdditiveGroup.coactComponent R (MvPolynomial (Fin 2) R) d (monomial e c) =
      monomial (Finsupp.single 0 (e 0 + d)) (c * (-1 : R) ^ d) := by
  rw [AdditiveGroup.coactComponent_apply, gaShear_coact_monomial, map_sum]
  rw [Finset.sum_eq_single d]
  · rw [_root_.LinearMap.tensorComponent_tmul, AdditiveGroup.coeff_pow, ite_eq_left rfl, one_smul,
      h, Nat.sub_self, Finsupp.single_zero, add_zero, Nat.choose_self, Nat.cast_one, mul_one]
  · intro k _ hkd
    rw [_root_.LinearMap.tensorComponent_tmul, AdditiveGroup.coeff_pow, ite_eq_right hkd, zero_smul]
  · intro hnd
    exact (hnd (Finset.mem_range.mpr (by omega))).elim

/-- **The `𝔾ₐ`-coinvariant subalgebra of `R[x, y]` is `R[x]`**, over every commutative ring `R`
(in arbitrary characteristic). -/
theorem gaShearCoinvariants_eq_adjoin_X_zero :
    gaShearCoinvariants R = Algebra.adjoin R {X (0 : Fin 2)} := by
  classical
  refine le_antisymm ?_ (Algebra.adjoin_le ?_)
  · intro p hp
    have hcoact :
        Comodule.coact (R := R) (C := SymmetricAlgebra R R) p =
          p ⊗ₜ[R] (1 : SymmetricAlgebra R R) :=
      mem_gaShearCoinvariants.mp hp
    have hy0 : ∀ e ∈ p.support, e 1 = 0 := by
      by_contra hnot
      push Not at hnot
      obtain ⟨e, he, he1⟩ := hnot
      obtain ⟨e₀, he₀, hmax⟩ := Finset.exists_max_image p.support (fun m ↦ m 1) ⟨e, he⟩
      set d := e₀ 1 with hd_def
      have hdpos : 0 < d := lt_of_lt_of_le (Nat.pos_of_ne_zero he1) (hmax e he)
      have hcomp0 : AdditiveGroup.coactComponent R (MvPolynomial (Fin 2) R) d p = 0 := by
        rw [AdditiveGroup.coactComponent_apply, hcoact, _root_.LinearMap.tensorComponent_tmul]
        have h1 : AdditiveGroup.coeff R d (1 : SymmetricAlgebra R R) = 0 := by
          simpa [pow_zero, hdpos.ne] using AdditiveGroup.coeff_pow R 0 d
        rw [h1, zero_smul]
      have hcoeff :
          (AdditiveGroup.coactComponent R (MvPolynomial (Fin 2) R) d p).coeff
              (Finsupp.single 0 (e₀ 0 + d)) = 0 := by
        rw [hcomp0, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
      conv_lhs at hcoeff => rw [p.as_sum, map_sum, coeff_sum]
      rw [Finset.sum_eq_single e₀] at hcoeff
      · rw [gaShear_coactComponent_monomial_of_eq R hd_def.symm, coeff_monomial,
          ite_eq_left rfl] at hcoeff
        have hmul := congrArg (· * (-1 : R) ^ d) hcoeff
        simp only [zero_mul, mul_assoc, ← mul_pow, neg_one_mul, neg_neg, one_pow, mul_one] at hmul
        exact (mem_support_iff.mp he₀) hmul
      · intro m hm hme₀
        rcases lt_or_eq_of_le (hmax m hm) with hlt | heq
        · rw [gaShear_coactComponent_monomial_of_lt R hlt, AddMonoidAlgebra.coeff_zero,
            Finsupp.zero_apply]
        · rw [gaShear_coactComponent_monomial_of_eq R heq, coeff_monomial]
          have hne : Finsupp.single (0 : Fin 2) (m 0 + d) ≠ Finsupp.single 0 (e₀ 0 + d) := by
            intro hsing
            have h0 : m 0 + d = e₀ 0 + d := by
              simpa using congrArg (fun f : Fin 2 →₀ ℕ ↦ f 0) hsing
            apply hme₀
            refine Finsupp.ext fun i ↦ ?_
            fin_cases i
            · exact Nat.add_right_cancel h0
            · exact heq
          exact ite_eq_right hne
      · intro hne₀
        exact (hne₀ he₀).elim
    rw [p.as_sum]
    refine Subalgebra.sum_mem _ fun e he ↦ ?_
    have he' : e = Finsupp.single 0 (e 0) := by
      refine Finsupp.ext fun i ↦ ?_
      fin_cases i
      · simp
      · simpa using hy0 e he
    rw [he', ← C_mul_X_pow_eq_monomial, ← MvPolynomial.algebraMap_eq]
    exact mul_mem (Subalgebra.algebraMap_mem _ _)
      (pow_mem (Algebra.subset_adjoin (Set.mem_singleton _)) (e 0))
  · rintro _ rfl
    rw [SetLike.mem_coe, mem_gaShearCoinvariants]
    exact gaShearComoduleAlgebra_coact_X_zero R

/-- The singleton `{x}` is a SAGBI basis of the `𝔾ₐ`-coinvariant subalgebra for every monomial
order on `Fin 2`. -/
theorem isSAGBIBasis_singleton_X_zero_gaShearCoinvariants (m : MonomialOrder (Fin 2)) :
    m.IsSAGBIBasis {X (0 : Fin 2)} (gaShearCoinvariants R) := by
  rw [gaShearCoinvariants_eq_adjoin_X_zero, X]
  exact m.isSAGBIBasis_singleton_monomial (Finsupp.single 0 1)

end CommRing

section Field

universe u

/-- Over any field, the additive group `𝔾ₐ` has connected prime spectrum. -/
theorem connectedSpace_primeSpectrum_ga (k : Type u) [Field k] :
    ConnectedSpace (PrimeSpectrum (SymmetricAlgebra k k)) :=
  RingHom.connectedSpace_primeSpectrum_of_injective
    (AdditiveGroup.coordinateAlgEquiv k).toRingHom
    (AdditiveGroup.coordinateAlgEquiv k).injective

/-- **The additive group `𝔾ₐ` is not reductive** over any field `k`: it is smooth unipotent with
nontrivial geometric fibre, whereas a reductive group whose geometric fibre has only unipotent
geometric points has trivial geometric fibre. -/
theorem not_reductiveCommHopfAlgProperty_ga (k : Type u) [Field k] :
    ¬ reductiveCommHopfAlgProperty k
      (FiniteTypeCommHopfAlgCat.of k (SymmetricAlgebra k k)) := by
  intro hred
  have hunip :
      geometricallyUnipotentPointsCommHopfAlgProperty (AlgebraicClosure k)
        (FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k)
          (FiniteTypeCommHopfAlgCat.of k (SymmetricAlgebra k k))).obj :=
    (geometricallyUnipotentPointsCommHopfAlgProperty (AlgebraicClosure k)).prop_of_iso
      (AdditiveGroup.coordinateHopfAlgebraBaseChangeIso k (AlgebraicClosure k)).symm
      (AdditiveGroup.geometricallyUnipotentPointsCommHopfAlgProperty_coordinateHopfAlgebra
        (AlgebraicClosure k))
  let e := hred.geometricFiberCounitBialgEquiv hunip
  let x : AlgebraicClosure k ⊗[k] SymmetricAlgebra k k :=
    (1 : AlgebraicClosure k) ⊗ₜ[k] SymmetricAlgebra.ι k k 1
  have hx : e x = e 0 := by
    rw [map_zero, reductiveCommHopfAlgProperty.geometricFiberCounitBialgEquiv_apply]
    simp [x, SymmetricAlgebra.counit_ι]
  have hx0 : x = 0 := e.injective hx
  have hι : SymmetricAlgebra.ι (AlgebraicClosure k) (AlgebraicClosure k) 1 = 0 := by
    simpa [x, AdditiveGroup.gaScalarTensorBialgEquiv_tmul_ι] using
      congrArg (AdditiveGroup.gaScalarTensorBialgEquiv (k := k) (K := AlgebraicClosure k)) hx0
  exact (AdditiveGroup.monomialBasis (AlgebraicClosure k)).ne_zero 1 (by
    simpa [AdditiveGroup.monomialBasis_apply] using hι)

/-- **Connected non-reductive boundary example over `ℂ`:** the connected smooth unipotent group
`𝔾ₐ ≤ GL₂` acting on `ℂ[x, y]` by the contragredient shear coaction has coinvariant subalgebra
`ℂ[x]` with singleton SAGBI basis `{x}` for every monomial order, while `𝔾ₐ` is neither linearly
reductive nor reductive. -/
theorem gaShearCoinvariants_complex_boundary :
    gaShearCoinvariants ℂ = Algebra.adjoin ℂ {X (0 : Fin 2)} ∧
    (∀ m : MonomialOrder (Fin 2),
      m.IsSAGBIBasis {X (0 : Fin 2)} (gaShearCoinvariants ℂ)) ∧
    ConnectedSpace (PrimeSpectrum (SymmetricAlgebra ℂ ℂ)) ∧
    geometricallyConnectedCommHopfAlgProperty ℂ (AdditiveGroup.coordinateHopfAlgebra ℂ) ∧
    smoothUnipotentCommHopfAlgProperty ℂ
      (FiniteTypeCommHopfAlgCat.of ℂ (SymmetricAlgebra ℂ ℂ)) ∧
    ¬ Coalgebra.IsLinearlyReductive.{0, 0, 0} ℂ (SymmetricAlgebra ℂ ℂ) ∧
    ¬ reductiveCommHopfAlgProperty ℂ
      (FiniteTypeCommHopfAlgCat.of ℂ (SymmetricAlgebra ℂ ℂ)) :=
  ⟨gaShearCoinvariants_eq_adjoin_X_zero ℂ,
    isSAGBIBasis_singleton_X_zero_gaShearCoinvariants ℂ,
    connectedSpace_primeSpectrum_ga ℂ,
    AdditiveGroup.geometricallyConnectedCommHopfAlgProperty_coordinateHopfAlgebra ℂ,
    AdditiveGroup.smoothUnipotentCommHopfAlgProperty_coordinateHopfAlgebra ℂ,
    AdditiveGroup.not_isLinearlyReductive ℂ,
    not_reductiveCommHopfAlgProperty_ga ℂ⟩

end Field

end GaShear

end TauCeti
