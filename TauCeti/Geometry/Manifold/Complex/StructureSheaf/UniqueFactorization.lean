/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Complex.StructureSheaf.Domain
public import TauCeti.Geometry.Manifold.Complex.StructureSheaf.Weierstrass
public import TauCeti.RingTheory.Polynomial.Rueckert

import Mathlib.Analysis.Normed.Module.FiniteDimension
import TauCeti.Analysis.Analytic.Uniqueness
import TauCeti.Geometry.Manifold.Complex.Analytic
import TauCeti.Geometry.Manifold.Complex.StructureSheaf.StalkPullback
import TauCeti.RingTheory.Polynomial.Distinguished

/-!
# Unique factorization in holomorphic stalks

At every point `x` of a finite-dimensional complex manifold `X` without boundary, the stalk
`𝒪_{X, x}` of the holomorphic structure sheaf is a unique factorization domain (Rückert's
factoriality theorem). By `UniqueFactorizationMonoid.instIsIntegrallyClosed`, holomorphic stalks
are therefore integrally closed domains.

On a finite-dimensional product `E × ℂ` at any base point `(x₀, w₀)`, vertical polynomial
evaluation `evalVertical x₀ w₀ : (𝒪_{E, x₀})[X] →+* 𝒪_{E × ℂ, (x₀, w₀)}` satisfies the abstract
Rückert hypotheses (`RingHom.IsRueckert`) with respect to the polynomials distinguished at the
maximal ideal of `𝒪_{E, x₀}`:

* monic divisors of distinguished polynomials remain distinguished because the maximal ideal is
  radical (`Polynomial.IsDistinguishedAt.of_dvd`);
* Weierstrass division identifies `(𝒪_{E, x₀})[X] ⧸ (P)` with
  `𝒪_{E × ℂ, (x₀, w₀)} ⧸ (evalVertical x₀ w₀ P)`;
* every nonzero germ in `𝒪_{E × ℂ, (x₀, w₀)}` becomes regular in the vertical variable after an
  affine linear automorphism fixing `(x₀, w₀)`, and Weierstrass preparation expresses the
  transformed germ as a unit multiple of `evalVertical x₀ w₀ P` for some distinguished `P`.

Induction on `Module.finrank ℂ E` via `RingHom.IsRueckert.uniqueFactorizationMonoid` establishes
unique factorization on model spaces, chart pullback transfers it to arbitrary complex manifolds
without boundary, and `smoothStalkIso` transfers it to the stalks of Mathlib's complex-smooth
structure sheaf. Consequently, for a distinguished polynomial `P`, primality and irreducibility of
`evalVertical x₀ w₀ P` in `𝒪_{E × ℂ, (x₀, w₀)}` are equivalent to primality and irreducibility of
`P` in `(𝒪_{E, x₀})[X]`; in particular, every Eisenstein polynomial of positive degree over
`𝒪_{E, x₀}` defines a prime holomorphic hypersurface germ.

## Main declarations

* `TauCeti.holomorphicStructureSheaf.isRueckert_evalVertical`: vertical polynomial evaluation
  `(𝒪_{E, x₀})[X] →+* 𝒪_{E × ℂ, (x₀, w₀)}` satisfies `RingHom.IsRueckert` for the polynomials
  distinguished at the maximal ideal of `𝒪_{E, x₀}`.
* `TauCeti.holomorphicStructureSheaf.stalkUniqueFactorizationMonoid`,
  `TauCeti.holomorphicStructureSheaf.smoothStalkUniqueFactorizationMonoid`: holomorphic and
  complex-smooth stalks on a finite-dimensional complex manifold without boundary are unique
  factorization domains.
* `TauCeti.holomorphicStructureSheaf.isPrime_span_evalVertical_iff`,
  `TauCeti.holomorphicStructureSheaf.prime_evalVertical_iff`,
  `TauCeti.holomorphicStructureSheaf.irreducible_evalVertical_iff`: for a distinguished polynomial
  `P`, `(evalVertical x₀ w₀ P)` is prime (equivalently irreducible) in `𝒪_{E × ℂ, (x₀, w₀)}` if
  and only if `P` is prime (equivalently irreducible) in `(𝒪_{E, x₀})[X]`.
* `TauCeti.holomorphicStructureSheaf.prime_evalVertical_of_isEisensteinAt`,
  `TauCeti.holomorphicStructureSheaf.irreducible_evalVertical_of_isEisensteinAt`,
  `TauCeti.holomorphicStructureSheaf.prime_evalVertical_X_pow_sub_C`: Eisenstein polynomials of
  positive degree—and in particular `X ^ n - C h` for `h ∈ 𝔪_{x₀} \ 𝔪_{x₀}²`—define prime
  holomorphic germs.

## References

* R. C. Gunning, H. Rossi, *Analytic Functions of Several Complex Variables*, Chapter II, §B.
* H. Grauert, R. Remmert, *Coherent Analytic Sheaves*, Chapter 2, §1.
* S. Bosch, U. Güntzer, R. Remmert, *Non-Archimedean Analysis*, §5.2.5.
-/

public noncomputable section

open Filter Function Module Polynomial Topology
open scoped ContDiff Manifold

namespace TauCeti.holomorphicStructureSheaf

section Rueckert

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Every nonzero holomorphic germ at `p = (x₀, w₀)` can be moved by a stalk automorphism to a
germ whose vertical power series has nonzero residue-field reduction. -/
private theorem exists_ringEquiv_map_residue_verticalPowerSeries_ne_zero {x₀ : E} {w₀ : ℂ}
    {b : (holomorphicStructureSheaf 𝓘(ℂ, E × ℂ) (E × ℂ)).presheaf.stalk (x₀, w₀)} (hb : b ≠ 0) :
    ∃ α : (holomorphicStructureSheaf 𝓘(ℂ, E × ℂ) (E × ℂ)).presheaf.stalk (x₀, w₀) ≃+*
        (holomorphicStructureSheaf 𝓘(ℂ, E × ℂ) (E × ℂ)).presheaf.stalk (x₀, w₀),
      (verticalPowerSeries x₀ w₀ (α b)).map
        (IsLocalRing.residue ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀)) ≠ 0 := by
  let p : E × ℂ := (x₀, w₀)
  obtain ⟨F, hF, hbF⟩ := exists_analyticAt_toFilterGerm_eq p b
  -- Choose linear coordinates `L` making `F ∘ L` regular in the vertical variable at `(x₁, w₁)`.
  obtain ⟨L, ⟨x₁, w₁⟩, hLq, hslice⟩ := hF.exists_continuousLinearEquiv_analyticOrderAt_ne_top
    ((eq_zero_iff_of_toFilterGerm_eq (hbF _ le_rfl)).not.1 hb)
  -- Re-center `L` into an affine biholomorphism `Φ` fixing `p = (x₀, w₀)`.
  let Φ : E × ℂ → E × ℂ := fun z ↦ p + L (z - p)
  let Ψ : E × ℂ → E × ℂ := fun z ↦ p + L.symm (z - p)
  have hΦp : Φ p = p := by simp [Φ]
  have hΦ : ContMDiff 𝓘(ℂ, E × ℂ) 𝓘(ℂ, E × ℂ) ω Φ :=
    contMDiff_iff_contDiff.2 (contDiff_const.add (L.contDiff.comp (contDiff_id.sub contDiff_const)))
  have hΨ : ContMDiff 𝓘(ℂ, E × ℂ) 𝓘(ℂ, E × ℂ) ω Ψ := contMDiff_iff_contDiff.2
    (contDiff_const.add (L.symm.contDiff.comp (contDiff_id.sub contDiff_const)))
  have hbij : Bijective (stalkPullback (a := p) (Eventually.of_forall fun _ ↦ hΦ.contMDiffAt)) :=
    stalkPullback_bijective _ (Eventually.of_forall fun _ ↦ hΨ.contMDiffAt)
      (Eventually.of_forall fun z ↦ by simp [Φ, Ψ])
      (Eventually.of_forall fun z ↦ by simp [Φ, Ψ])
  let α := (RingEquiv.cast
    (R := fun z ↦ (holomorphicStructureSheaf 𝓘(ℂ, E × ℂ) (E × ℂ)).presheaf.stalk z)
    hΦp.symm).trans (RingEquiv.ofBijective _ hbij)
  have hαb : toFilterGerm 𝓘(ℂ, E × ℂ) (E × ℂ) p (𝓝 p) le_rfl (α b) = ↑(F ∘ Φ) := by
    simp only [α, RingEquiv.trans_apply, RingEquiv.ofBijective_apply, toFilterGerm_stalkPullback,
      toFilterGerm_ringEquivCast hΦp.symm (hbF _ le_rfl), Germ.coe_compTendsto]
  refine ⟨α, (map_residue_verticalPowerSeries_ne_zero_iff hαb).2 ?_⟩
  -- Translating `t ↦ w₀ + (t - w₁)` identifies the vertical slice of `F ∘ Φ` with
  -- `t ↦ F (L (x₁, t))`.
  rw [Ne, analyticOrderAt_eq_top]
  intro hord
  apply hslice
  rw [analyticOrderAt_eq_top]
  have ht : Tendsto (fun t : ℂ ↦ w₀ + (t - w₁)) (𝓝 w₁) (𝓝 w₀) := by
    have : Continuous fun t : ℂ ↦ w₀ + (t - w₁) := by fun_prop
    simpa using this.tendsto w₁
  refine (ht.eventually hord).mono fun t ht0 ↦ ?_
  have hΦ_slice : Φ (x₀, w₀ + (t - w₁)) = L (x₁, t) := by
    have hsub : ((x₀, w₀ + (t - w₁)) - p : E × ℂ) = ((0 : E), t - w₁) := by ext <;> simp [p]
    dsimp only [Φ]
    rw [hsub, ← hLq, ← map_add]
    congr 1; ext <;> simp
  simpa [Function.comp_apply, hΦ_slice] using ht0

variable [FiniteDimensional ℂ E]

/-- **Holomorphic stalks satisfy the Rückert hypotheses.** At any point `(x₀, w₀) : E × ℂ` of a
finite-dimensional product, vertical polynomial evaluation
`evalVertical x₀ w₀ : (𝒪_{E, x₀})[X] →+* 𝒪_{E × ℂ, (x₀, w₀)}` satisfies `RingHom.IsRueckert` with
respect to the polynomials distinguished at the maximal ideal of `𝒪_{E, x₀}`. -/
theorem isRueckert_evalVertical (x₀ : E) (w₀ : ℂ) :
    (evalVertical x₀ w₀).IsRueckert
      {P | P.IsDistinguishedAt
        (IsLocalRing.maximalIdeal ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀))} where
  injective := evalVertical_injective x₀ w₀
  monic hw := hw.monic
  mem_of_dvd hw hp hpw :=
    hw.of_dvd (IsLocalRing.maximalIdeal.isMaximal _).isPrime.isRadical hp hpw
  dvd_iff hw _ := (evalVertical_dvd_iff_of_isDistinguishedAt hw).symm
  exists_dvd_sub hw b := by
    obtain ⟨⟨q, r⟩, ⟨_, hb_eq⟩, _⟩ := existsUnique_weierstrassDivision_of_isDistinguishedAt hw b
    exact ⟨r, q, by linear_combination hb_eq⟩
  exists_mul_eq hb := by
    obtain ⟨α, hres⟩ := exists_ringEquiv_map_residue_verticalPowerSeries_ne_zero hb
    obtain ⟨⟨P, u⟩, ⟨hP, hu, hfac⟩, _⟩ := existsUnique_weierstrassPreparation hres
    refine ⟨α, hu.unit⁻¹, P, hP, ?_⟩
    rw [hfac, mul_comm (evalVertical x₀ w₀ P) u, ← mul_assoc, IsUnit.val_inv_mul, one_mul]

/-- A distinguished polynomial generates a prime ideal in `𝒪_{E × ℂ, (x₀, w₀)}` if and only if it
generates a prime ideal in `(𝒪_{E, x₀})[X]`. -/
theorem isPrime_span_evalVertical_iff {x₀ : E} {w₀ : ℂ}
    {P : ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀)[X]}
    (hP : P.IsDistinguishedAt
      (IsLocalRing.maximalIdeal ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀))) :
    (Ideal.span {evalVertical x₀ w₀ P}).IsPrime ↔ (Ideal.span {P}).IsPrime := by
  rw [← Ideal.Quotient.isDomain_iff_prime, ← Ideal.Quotient.isDomain_iff_prime]
  exact (MulEquiv.isDomain_iff (quotientEquivOfIsDistinguishedAt x₀ w₀ hP).toMulEquiv).symm

/-- For a distinguished polynomial `P`, `evalVertical x₀ w₀ P` is prime in `𝒪_{E × ℂ, (x₀, w₀)}`
if and only if `P` is prime in `(𝒪_{E, x₀})[X]`. -/
theorem prime_evalVertical_iff {x₀ : E} {w₀ : ℂ}
    {P : ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀)[X]}
    (hP : P.IsDistinguishedAt
      (IsLocalRing.maximalIdeal ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀))) :
    Prime (evalVertical x₀ w₀ P) ↔ Prime P := by
  have hP0 : evalVertical x₀ w₀ P ≠ 0 :=
    (map_ne_zero_iff _ (evalVertical_injective x₀ w₀)).2 hP.monic.ne_zero
  rw [← Ideal.span_singleton_prime hP0, ← Ideal.span_singleton_prime hP.monic.ne_zero,
    isPrime_span_evalVertical_iff hP]

end Rueckert

section ModelSpace

/-- On a zero-dimensional complex normed space, evaluation identifies every holomorphic stalk with
`ℂ`, which is a unique factorization domain. -/
private theorem uniqueFactorizationMonoid_stalk_of_finrank_eq_zero {V : Type}
    [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
    (hV : finrank ℂ V = 0) (x : V) :
    UniqueFactorizationMonoid ((holomorphicStructureSheaf 𝓘(ℂ, V) V).presheaf.stalk x) := by
  have hV' : ∀ y : V, y = x := fun y ↦
    (finrank_zero_iff_forall_zero.1 hV y).trans (finrank_zero_iff_forall_zero.1 hV x).symm
  refine (RingEquiv.ofBijective (eval 𝓘(ℂ, V) V x)
    ⟨(injective_iff_map_eq_zero _).2 fun s hs ↦ ?_, eval_surjective _ _ x⟩).symm.toMulEquiv
    |>.uniqueFactorizationMonoid inferInstance
  obtain ⟨φ, -, hφ⟩ := exists_toFilterGerm_eq x s
  refine (eq_zero_iff_of_toFilterGerm_eq (hφ _ le_rfl)).2 (Eventually.of_forall fun y ↦ ?_)
  rw [hV' y, ← eval_eq_of_toFilterGerm_eq (hφ _ le_rfl), hs, Pi.zero_apply]

/-- Holomorphic stalks of a finite-dimensional complex normed space are unique factorization
domains, by induction on the complex dimension via Rückert's descent. -/
private theorem uniqueFactorizationMonoid_stalk_of_finrank_eq :
    ∀ (n : ℕ) (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V],
      finrank ℂ V = n → ∀ x : V,
        UniqueFactorizationMonoid ((holomorphicStructureSheaf 𝓘(ℂ, V) V).presheaf.stalk x)
  | 0, _, _, _, _, hV, x => uniqueFactorizationMonoid_stalk_of_finrank_eq_zero hV x
  | n + 1, V, _, _, _, hV, x => by
    let e : V ≃L[ℂ] (Fin n → ℂ) × ℂ := ContinuousLinearEquiv.ofFinrankEq (by simp [hV])
    have : UniqueFactorizationMonoid
        ((holomorphicStructureSheaf 𝓘(ℂ, Fin n → ℂ) (Fin n → ℂ)).presheaf.stalk (e x).1) :=
      uniqueFactorizationMonoid_stalk_of_finrank_eq n (Fin n → ℂ) (by simp) (e x).1
    have hprod : UniqueFactorizationMonoid
        ((holomorphicStructureSheaf 𝓘(ℂ, (Fin n → ℂ) × ℂ) ((Fin n → ℂ) × ℂ)).presheaf.stalk
          (e x)) := by
      simpa only [Prod.mk.eta] using
        (isRueckert_evalVertical (e x).1 (e x).2).uniqueFactorizationMonoid
    exact (RingEquiv.ofBijective _ (e.holomorphicStalkPullback_bijective x)).toMulEquiv
      |>.uniqueFactorizationMonoid hprod

end ModelSpace

section Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℂ E H} [I.Boundaryless]
  {X : Type} [TopologicalSpace X] [ChartedSpace H X] [IsManifold I 1 X]

/-- **Rückert's unique factorization theorem.** The stalk of holomorphic functions at any point of
a finite-dimensional complex manifold without boundary is a unique factorization domain. -/
instance stalkUniqueFactorizationMonoid (x : X) :
    UniqueFactorizationMonoid ((holomorphicStructureSheaf I X).presheaf.stalk x) := by
  have : IsManifold I ω X := IsManifold.of_ne_zero ω one_ne_zero inferInstance
  let e : E ≃L[ℂ] Fin (finrank ℂ E) → ℂ := ContinuousLinearEquiv.ofFinrankEq (by simp)
  have hmodel := uniqueFactorizationMonoid_stalk_of_finrank_eq _ (Fin (finrank ℂ E) → ℂ) rfl
    ((e ∘ extChartAt I x) x)
  exact (RingEquiv.ofBijective _ (stalkPullback_comp_extChartAt_bijective x e)).toMulEquiv
    |>.uniqueFactorizationMonoid hmodel

/-- A stalk of Mathlib's complex-smooth structure sheaf on a finite-dimensional complex manifold
without boundary is a unique factorization domain, via its comparison with holomorphic germs. -/
instance smoothStalkUniqueFactorizationMonoid (x : X) :
    UniqueFactorizationMonoid ((smoothSheafCommRing I 𝓘(ℂ) X ℂ).presheaf.stalk x) :=
  (smoothStalkIso I X x).commRingCatIsoToRingEquiv.toMulEquiv.uniqueFactorizationMonoid
    inferInstance

end Manifold

section Irreducibility

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]

/-- For a distinguished polynomial `P` over `𝒪_{E, x₀}`, `evalVertical x₀ w₀ P` is irreducible in
`𝒪_{E × ℂ, (x₀, w₀)}` if and only if `P` is irreducible in `(𝒪_{E, x₀})[X]`. -/
theorem irreducible_evalVertical_iff {x₀ : E} {w₀ : ℂ}
    {P : ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀)[X]}
    (hP : P.IsDistinguishedAt
      (IsLocalRing.maximalIdeal ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀))) :
    Irreducible (evalVertical x₀ w₀ P) ↔ Irreducible P := by
  rw [UniqueFactorizationMonoid.irreducible_iff_prime,
    UniqueFactorizationMonoid.irreducible_iff_prime, prime_evalVertical_iff hP]

/-- **Analytic Eisenstein primality criterion.** If `P : (𝒪_{E, x₀})[X]` of positive degree is
Eisenstein at the maximal ideal of `𝒪_{E, x₀}`, then `evalVertical x₀ w₀ P` is prime in
`𝒪_{E × ℂ, (x₀, w₀)}`. -/
theorem prime_evalVertical_of_isEisensteinAt {x₀ : E} {w₀ : ℂ}
    {P : ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀)[X]}
    (hP : P.IsEisensteinAt
      (IsLocalRing.maximalIdeal ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀)))
    (hdeg : 0 < P.natDegree) :
    Prime (evalVertical x₀ w₀ P) := by
  -- Scale `P` by the inverse of its unit leading coefficient to obtain a monic Eisenstein `Q`.
  let A := (holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀
  obtain ⟨u, hu⟩ := IsLocalRing.notMem_maximalIdeal.mp hP.leading
  let Q : A[X] := C (↑u⁻¹ : A) * P
  have hQ_deg : Q.natDegree = P.natDegree := natDegree_C_mul_eq_of_mul_eq_one u.mul_inv
  have hQ_mo : Q.Monic := monic_C_mul_of_mul_leadingCoeff_eq_one (by simp [← hu])
  have hQ_dist : Q.IsDistinguishedAt (IsLocalRing.maximalIdeal A) :=
    ⟨⟨fun {n} hn ↦ by
      rw [coeff_C_mul]
      exact Ideal.mul_mem_left _ _ (hP.mem (hQ_deg ▸ hn))⟩, hQ_mo⟩
  have hQ_eis : Q.IsEisensteinAt (IsLocalRing.maximalIdeal A) :=
    hQ_mo.isEisensteinAt_of_mem_of_notMem (IsLocalRing.maximalIdeal.isMaximal _).ne_top
      (fun hn ↦ hQ_dist.1.mem hn) fun h ↦ hP.notMem <| by
        have hmul := Ideal.mul_mem_left _ (u : A) h
        rwa [coeff_C_mul, ← mul_assoc, Units.mul_inv, one_mul] at hmul
  have hQ_irr : Irreducible Q := hQ_eis.irreducible
    (IsLocalRing.maximalIdeal.isMaximal _).isPrime hQ_mo.isPrimitive (hQ_deg ▸ hdeg)
  have hQ_prime : Prime (evalVertical x₀ w₀ Q) := (prime_evalVertical_iff hQ_dist).2 hQ_irr.prime
  have hPQ : P = C (u : A) * Q := by simp [Q, ← mul_assoc, ← C_mul]
  rw [hPQ, map_mul]
  exact (associated_unit_mul_left (evalVertical x₀ w₀ Q) (evalVertical x₀ w₀ (C (u : A)))
    ((u.isUnit.map C).map (evalVertical x₀ w₀))).symm.prime hQ_prime

/-- If `P : (𝒪_{E, x₀})[X]` of positive degree is Eisenstein at the maximal ideal of `𝒪_{E, x₀}`,
then `evalVertical x₀ w₀ P` is irreducible in `𝒪_{E × ℂ, (x₀, w₀)}`. -/
theorem irreducible_evalVertical_of_isEisensteinAt {x₀ : E} {w₀ : ℂ}
    {P : ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀)[X]}
    (hP : P.IsEisensteinAt
      (IsLocalRing.maximalIdeal ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀)))
    (hdeg : 0 < P.natDegree) :
    Irreducible (evalVertical x₀ w₀ P) :=
  (prime_evalVertical_of_isEisensteinAt hP hdeg).irreducible

/-- For `h ∈ 𝔪_{x₀} \ 𝔪_{x₀}²` and `n ≠ 0`, the branched-cover polynomial `X ^ n - C h` evaluates
to a prime holomorphic germ in `𝒪_{E × ℂ, (x₀, w₀)}`. -/
theorem prime_evalVertical_X_pow_sub_C {x₀ : E} {w₀ : ℂ}
    {h : (holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀}
    (hh : h ∈ IsLocalRing.maximalIdeal ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀))
    (hh2 : h ∉
      IsLocalRing.maximalIdeal ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀) ^ 2)
    {n : ℕ} (hn : n ≠ 0) :
    Prime (evalVertical x₀ w₀ (X ^ n - C h)) := by
  have hmo := monic_X_pow_sub_C h hn
  have hdeg : (X ^ n - C h).natDegree = n := natDegree_X_pow_sub_C h
  refine prime_evalVertical_of_isEisensteinAt
    (hmo.isEisensteinAt_of_mem_of_notMem (IsLocalRing.maximalIdeal.isMaximal _).ne_top
      (fun {i} hi ↦ ?_) ?_) (hdeg.symm ▸ Nat.pos_of_ne_zero hn)
  · have hin : i ≠ n := (hdeg ▸ hi).ne
    rw [coeff_sub, coeff_X_pow, ite_eq_right hin, zero_sub, neg_mem_iff]
    rcases eq_or_ne i 0 with rfl | hi0
    · simpa using hh
    · simp [coeff_C, hi0]
  · simpa [coeff_X_pow, hn.symm] using hh2

end Irreducibility

end TauCeti.holomorphicStructureSheaf
