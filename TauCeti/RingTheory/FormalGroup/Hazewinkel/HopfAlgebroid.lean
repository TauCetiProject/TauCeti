/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.Data.ZMod.Basic
public import Mathlib.RingTheory.Ideal.Int
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import TauCeti.Algebra.MvPolynomial.Lift
public import TauCeti.RingTheory.FormalGroup.CoordinateChange.HopfAlgebroid
public import TauCeti.RingTheory.FormalGroup.Hazewinkel.CoordinateChange
import Mathlib.Algebra.CharP.Invertible
import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Tactic.LinearCombination
import TauCeti.RingTheory.FormalGroup.Hazewinkel.LeadingDifference
import TauCeti.RingTheory.FormalGroup.Hazewinkel.NSMul
import TauCeti.RingTheory.FormalGroup.Logarithm.Basic

/-!
# The Hazewinkel and Brown–Peterson Hopf algebroid of strict `p`-typical coordinate changes

For a prime `p`, let `V = MvPolynomial ℕ+ ℤ` and `Γ_p = MvPolynomial ℕ+ V`. Homomorphisms
`V →+* R` classify `hazewinkelIntegralFormalGroup p v` (`TauCeti.Hazewinkel.hom_ext`), while
`Γ_p →+* R` classifies pairs `(v, t)` encoding `pTypicalStrictCoordinate p t` via
`MvPolynomial.prodHomEquiv`. Integral invariance and rational-to-integral descent equip `(V, Γ_p)`
with a **Hopf algebroid** structure (`TauCeti.Hazewinkel.rightUnit`, `TauCeti.Hazewinkel.counit`,
`TauCeti.Hazewinkel.tensorLift`, `TauCeti.Hazewinkel.coproduct`,
`TauCeti.Hazewinkel.conjugation`) receiving a canonical morphism from the Lazard Hopf algebroid
(`TauCeti.Hazewinkel.ofLazardRing`, `TauCeti.Hazewinkel.ofLazardCoordinateChange`);
`TauCeti.Hazewinkel.tensorLift` instantiates the general polynomial pushout
`MvPolynomial.pushoutEquiv`.

When primes `q ≠ p` are units in `R`, `(V, Γ_p)` (and its `p`-local base change
`(A[v₁, v₂, …], A[v₁, v₂, …][t₁, t₂, …])`) classifies all strict isomorphisms between Hazewinkel
laws (`TauCeti.Hazewinkel.strictIsoEquiv`, `TauCeti.Hazewinkel.strictIsoAlgEquiv`,
`TauCeti.Hazewinkel.strictIsoAlgEquivOfAtPrime`, `TauCeti.Hazewinkel.strictIsoEquivOfCharP`).

Finally, we prove Ravenel's logarithm recursion
(`TauCeti.Hazewinkel.hazewinkelLogCoeff_comp_rightUnit`) and degree-one formulas
(`TauCeti.Hazewinkel.rightUnit_X_one`, `TauCeti.Hazewinkel.coproduct_X_one`,
`TauCeti.Hazewinkel.conjugation_X_one`), establish invariance of the ideal `(p, v₁, v₂, …)`
(`TauCeti.Hazewinkel.map_rightUnit_ker_eval_zero_mod`), and construct the quotient homomorphism
`TauCeti.Hazewinkel.milnorQuotient : Γ_p →+* 𝔽_p[t₁, t₂, …]` together with the descended
`𝔽_p`-algebra homomorphisms `TauCeti.Hazewinkel.milnorCoproduct` (given by
`Δ(t_{n + 1}) = t_{n + 1} ⊗ 1 + 1 ⊗ t_{n + 1} + ∑_{i < n} t_{i + 1} ⊗ t_{n - i}^(p^(i + 1))`)
and `TauCeti.Hazewinkel.milnorConjugation` (an involution satisfying the recursion
`c(t_{n + 1}) = -t_{n + 1} - ∑_{i < n} t_{i + 1} c(t_{n - i})^(p^(i + 1))`).

*Unformalized topological remark (Ravenel, Theorem 4.1.18; Milnor 1958).* The dual Steenrod algebra
is not formalized here. Informally, under Milnor's coproduct
`Δ(ξ_k) = ∑_{i = 0}^k ξ_{k - i}^(p^i) ⊗ ξ_i`, the conjugate Milnor generators `ζₙ = χ(ξₙ)` satisfy
`Δ(ζ_k) = ∑_{i = 0}^k ζ_i ⊗ ζ_{k - i}^(p^i)`, matching `milnorCoproduct` under `tₙ ↦ χ(ξₙ)` (onto
the polynomial part `P_* = 𝔽_p[ξ₁, ξ₂, …]` of the mod-`p` dual Steenrod algebra for odd `p`, and
onto `𝔽_2[ξ₁, ξ₂, …]` ungraded or `𝔽_2[ξ₁², ξ₂², …]` via `tₙ ↦ χ(ξₙ)²` in topological grading at
`p = 2`; mapping `tₙ ↦ ξₙ` instead matches the opposite coproduct).

## References

* D. Quillen, *On the formal group laws of unoriented and complex cobordism theory*, 1969.
* J. Milnor, *The Steenrod algebra and its dual*, Ann. of Math. (2) 67 (1958), 150–171.
* [M. Hazewinkel, *Formal Groups and Applications*][hazewinkel1978], Chapter IV.
* D. C. Ravenel, *Complex Cobordism and Stable Homotopy Groups of Spheres*, §4.1 (Theorem 4.1.18)
  and Appendix A2.1.
-/

public section

noncomputable section

open MvPolynomial

namespace TauCeti

namespace Hazewinkel

variable {R : Type*} [CommRing R] (p : ℕ) [hp : Fact p.Prime]

/-- A ring homomorphism out of `ℤ[v₁, v₂, …]` is uniquely determined by the base change of
`universalHazewinkelIntegralFormalGroup p` along it. -/
theorem hom_ext {f g : MvPolynomial ℕ+ ℤ →+* R}
    (h : (universalHazewinkelIntegralFormalGroup p).map f =
      (universalHazewinkelIntegralFormalGroup p).map g) : f = g := by
  rw [map_universalHazewinkelIntegralFormalGroup, map_universalHazewinkelIntegralFormalGroup] at h
  exact MvPolynomial.homEquiv.injective (hazewinkelIntegralFormalGroup_injective p h)

/-- **The universal `p`-typical strict coordinate** over `ℤ[v₁, v₂, …][t₁, t₂, …]`. -/
def universalStrictCoordinate : FormalCoordinate (MvPolynomial ℕ+ (MvPolynomial ℕ+ ℤ)) :=
  ((universalHazewinkelIntegralFormalGroup p).map C).pTypicalStrictCoordinate p X

theorem universalStrictCoordinate_def : universalStrictCoordinate p =
    ((universalHazewinkelIntegralFormalGroup p).map C).pTypicalStrictCoordinate p X := (rfl)

@[simp] theorem linearCoeff_universalStrictCoordinate :
    FormalCoordinate.linearCoeff (universalStrictCoordinate p) = 1 :=
  FormalGroup.linearCoeff_pTypicalStrictCoordinate _ _ _

theorem universalStrictCoordinate_mem_ker : universalStrictCoordinate p ∈
    (FormalCoordinate.linearCoeff (R := MvPolynomial ℕ+ (MvPolynomial ℕ+ ℤ))).ker :=
  FormalGroup.pTypicalStrictCoordinate_mem_ker_linearCoeff _ _ _

/-- Base change of `universalStrictCoordinate p` along `f : Γ_p →+* R` recovers the strict
`p`-typical coordinate with parameters `f ∘ X` on the base-changed Hazewinkel law. -/
theorem map_universalStrictCoordinate (f : MvPolynomial ℕ+ (MvPolynomial ℕ+ ℤ) →+* R) :
    FormalCoordinate.map f (universalStrictCoordinate p) =
      ((universalHazewinkelIntegralFormalGroup p).map (f.comp C)).pTypicalStrictCoordinate
        p (f ∘ X) := by
  rw [universalStrictCoordinate, FormalGroup.map_pTypicalStrictCoordinate, FormalGroup.map_comp]

theorem map_universalStrictCoordinate_mem_ker (f : MvPolynomial ℕ+ (MvPolynomial ℕ+ ℤ) →+* R) :
    FormalCoordinate.map f (universalStrictCoordinate p) ∈
      (FormalCoordinate.linearCoeff (R := R)).ker := by
  rw [map_universalStrictCoordinate]
  exact FormalGroup.pTypicalStrictCoordinate_mem_ker_linearCoeff _ _ _

/-- A ring homomorphism out of `Γ_p` is uniquely determined by its restriction along `C` and the
base change of `universalStrictCoordinate p` along it. -/
theorem ringHom_ext_universalStrictCoordinate {f g : MvPolynomial ℕ+ (MvPolynomial ℕ+ ℤ) →+* R}
    (hC : f.comp C = g.comp C)
    (hφ : FormalCoordinate.map f (universalStrictCoordinate p) =
      FormalCoordinate.map g (universalStrictCoordinate p)) : f = g := by
  rw [map_universalStrictCoordinate, map_universalStrictCoordinate, hC] at hφ
  exact ringHom_ext' hC
    (congrFun (FormalGroup.pTypicalStrictCoordinate_injective _ hp.out.one_lt hφ))

/-- Applying `MvPolynomial.prodHomEquiv vt` to `universalStrictCoordinate p` yields the strict
`p`-typical coordinate `(hazewinkelIntegralFormalGroup p vt.1).pTypicalStrictCoordinate p vt.2`. -/
@[simp] theorem map_prodHomEquiv_universalStrictCoordinate (vt : (ℕ+ → R) × (ℕ+ → R)) :
    FormalCoordinate.map (MvPolynomial.prodHomEquiv vt) (universalStrictCoordinate p) =
      (hazewinkelIntegralFormalGroup p vt.1).pTypicalStrictCoordinate p vt.2 := by
  have hv : ⇑(MvPolynomial.homEquiv.symm vt.1) ∘ X = vt.1 := MvPolynomial.homEquiv.right_inv vt.1
  rw [map_universalStrictCoordinate, MvPolynomial.prodHomEquiv_comp_C,
    map_universalHazewinkelIntegralFormalGroup, hv,
    (funext (MvPolynomial.prodHomEquiv_X vt) : ⇑(MvPolynomial.prodHomEquiv vt) ∘ X = vt.2)]

/-- The **right unit** `η_R : ℤ[v₁, v₂, …] →+* ℤ[v₁, v₂, …][t₁, t₂, …]`, classifying the target
Hazewinkel formal group law transported along `universalStrictCoordinate p`. -/
def rightUnit : MvPolynomial ℕ+ ℤ →+* MvPolynomial ℕ+ (MvPolynomial ℕ+ ℤ) :=
  homEquiv.symm (existsUnique_pTypicalStrictCoordinate_smul_hazewinkelIntegralFormalGroup p
    (C ∘ (X : ℕ+ → MvPolynomial ℕ+ ℤ)) X).choose

/-- `rightUnit p` classifies the universal Hazewinkel law transported along
`universalStrictCoordinate p`. -/
theorem map_rightUnit :
    (universalHazewinkelIntegralFormalGroup p).map (rightUnit p) =
      universalStrictCoordinate p • (universalHazewinkelIntegralFormalGroup p).map C := by
  have hX : ⇑(rightUnit p) ∘ X = _ := MvPolynomial.homEquiv.right_inv _
  rw [map_universalHazewinkelIntegralFormalGroup, hX,
    ← (existsUnique_pTypicalStrictCoordinate_smul_hazewinkelIntegralFormalGroup p
      (C ∘ (X : ℕ+ → MvPolynomial ℕ+ ℤ)) X).choose_spec.left,
    universalStrictCoordinate, map_universalHazewinkelIntegralFormalGroup]

/-- Along any `f : Γ_p →+* R`, `f ∘ rightUnit p` classifies the base-changed source Hazewinkel law
transported along `FormalCoordinate.map f (universalStrictCoordinate p)`. -/
theorem map_comp_rightUnit (f : MvPolynomial ℕ+ (MvPolynomial ℕ+ ℤ) →+* R) :
    (universalHazewinkelIntegralFormalGroup p).map (f.comp (rightUnit p)) =
      FormalCoordinate.map f (universalStrictCoordinate p) •
        (universalHazewinkelIntegralFormalGroup p).map (f.comp C) := by
  rw [← FormalGroup.map_comp, map_rightUnit, FormalGroup.map_smul, FormalGroup.map_comp]

section Counit

omit p hp

/-- The **counit** `ε : ℤ[v₁, v₂, …][t₁, t₂, …] →+* ℤ[v₁, v₂, …]`, sending `tᵢ ↦ 0`. -/
def counit : MvPolynomial ℕ+ (MvPolynomial ℕ+ ℤ) →+* MvPolynomial ℕ+ ℤ :=
  eval₂Hom (RingHom.id _) 0

@[simp] theorem counit_X (i : ℕ+) : counit (X i) = 0 := by simp [counit]

@[simp] theorem counit_comp_C : counit.comp C = RingHom.id (MvPolynomial ℕ+ ℤ) :=
  RingHom.ext (eval₂Hom_C _ _)

@[simp] theorem counit_C (a : MvPolynomial ℕ+ ℤ) : counit (C a) = a := eval₂Hom_C _ _ a

end Counit

@[simp] theorem map_counit_universalStrictCoordinate :
    FormalCoordinate.map counit (universalStrictCoordinate p) = 1 := by
  rw [map_universalStrictCoordinate, counit_comp_C, FormalGroup.map_id,
    (funext counit_X : ⇑counit ∘ X = 0), FormalGroup.pTypicalStrictCoordinate_zero]

@[simp] theorem counit_comp_rightUnit : counit.comp (rightUnit p) = RingHom.id _ :=
  hom_ext p <| by
    rw [map_comp_rightUnit, map_counit_universalStrictCoordinate, counit_comp_C, one_smul]

@[simp] theorem counit_rightUnit (a : MvPolynomial ℕ+ ℤ) : counit (rightUnit p a) = a :=
  RingHom.congr_fun (counit_comp_rightUnit p) a

/-! ### Full classification of strict isomorphisms over `p`-local and `𝔽_p`-algebras -/

/-- When primes `q ≠ p` are units in `R`, homomorphisms `Γ_p →+* R` classify all strict
isomorphisms between Hazewinkel formal group laws over `R`. -/
def strictIsoEquiv (hlocal : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) :
    {q : (ℕ+ → R) × (ℕ+ → R) × (FormalCoordinate.linearCoeff (R := R)).ker //
      q.2.2.val • hazewinkelIntegralFormalGroup p q.1 = hazewinkelIntegralFormalGroup p q.2.1} ≃
      (MvPolynomial ℕ+ (MvPolynomial ℕ+ ℤ) →+* R) where
  toFun q := MvPolynomial.prodHomEquiv (q.val.1,
    (existsUnique_pTypicalStrictCoordinate_eq_of_smul_eq p hlocal
      (MonoidHom.mem_ker.mp q.val.2.2.property) q.property).choose)
  invFun f := ⟨(f.comp C ∘ X, f.comp (rightUnit p) ∘ X,
    ⟨FormalCoordinate.map f (universalStrictCoordinate p),
      map_universalStrictCoordinate_mem_ker p f⟩), by
    simpa only [map_universalHazewinkelIntegralFormalGroup] using (map_comp_rightUnit p f).symm⟩
  left_inv := fun ⟨⟨v, w, φ⟩, hsmul⟩ ↦ by
    let t := (existsUnique_pTypicalStrictCoordinate_eq_of_smul_eq p hlocal
      (MonoidHom.mem_ker.mp φ.property) hsmul).choose
    have ht : φ.val = (hazewinkelIntegralFormalGroup p v).pTypicalStrictCoordinate p t :=
      (existsUnique_pTypicalStrictCoordinate_eq_of_smul_eq p hlocal
        (MonoidHom.mem_ker.mp φ.property) hsmul).choose_spec.left
    let f := MvPolynomial.prodHomEquiv (v, t)
    have hv : ⇑(f.comp C) ∘ X = v := funext (MvPolynomial.prodHomEquiv_C_X (v, t))
    have hφ : FormalCoordinate.map f (universalStrictCoordinate p) = φ.val :=
      (map_prodHomEquiv_universalStrictCoordinate p (v, t)).trans ht.symm
    refine Subtype.ext (Prod.ext hv (Prod.ext (hazewinkelIntegralFormalGroup_injective p <| by
      simpa only [map_universalHazewinkelIntegralFormalGroup, hv, hφ, hsmul] using
        map_comp_rightUnit p f) (Subtype.ext hφ)))
  right_inv f := by
    have h := (map_comp_rightUnit p f).symm
    rw [map_universalHazewinkelIntegralFormalGroup, map_universalHazewinkelIntegralFormalGroup] at h
    have ht := ((existsUnique_pTypicalStrictCoordinate_eq_of_smul_eq p hlocal
      (MonoidHom.mem_ker.mp (map_universalStrictCoordinate_mem_ker p f)) h).choose_spec.right
      (f ∘ X) (by rw [map_universalStrictCoordinate,
        map_universalHazewinkelIntegralFormalGroup])).symm
    dsimp only
    rw [ht, ← MvPolynomial.prodHomEquiv_symm_apply_fst f,
      ← MvPolynomial.prodHomEquiv_symm_apply_snd f, Prod.mk.eta]
    exact MvPolynomial.prodHomEquiv.apply_symm_apply f

section StrictIsoSimp

variable (hlocal : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R))
  (q : {q : (ℕ+ → R) × (ℕ+ → R) × (FormalCoordinate.linearCoeff (R := R)).ker //
    q.2.2.val • hazewinkelIntegralFormalGroup p q.1 = hazewinkelIntegralFormalGroup p q.2.1})
  (f : MvPolynomial ℕ+ (MvPolynomial ℕ+ ℤ) →+* R)

@[simp] theorem strictIsoEquiv_C_X (i : ℕ+) :
    strictIsoEquiv p hlocal q (C (X i)) = q.val.1 i := MvPolynomial.prodHomEquiv_C_X _ i

theorem strictIsoEquiv_comp_C_comp_X : ⇑((strictIsoEquiv p hlocal q).comp C) ∘ X = q.val.1 :=
  congrArg (fun r ↦ r.val.1) ((strictIsoEquiv p hlocal).symm_apply_apply q)

theorem strictIsoEquiv_comp_rightUnit_comp_X :
    ⇑((strictIsoEquiv p hlocal q).comp (rightUnit p)) ∘ X = q.val.2.1 :=
  congrArg (fun r ↦ r.val.2.1) ((strictIsoEquiv p hlocal).symm_apply_apply q)

@[simp] theorem strictIsoEquiv_rightUnit_X (i : ℕ+) :
    strictIsoEquiv p hlocal q (rightUnit p (X i)) = q.val.2.1 i :=
  congrFun (strictIsoEquiv_comp_rightUnit_comp_X p hlocal q) i

@[simp] theorem map_strictIsoEquiv_universalStrictCoordinate :
    FormalCoordinate.map (strictIsoEquiv p hlocal q) (universalStrictCoordinate p) =
      q.val.2.2.val :=
  congrArg (fun r ↦ r.val.2.2.val) ((strictIsoEquiv p hlocal).symm_apply_apply q)

@[simp] theorem strictIsoEquiv_symm_fst :
    ((strictIsoEquiv p hlocal).symm f).val.1 = f.comp C ∘ X := (rfl)

@[simp] theorem strictIsoEquiv_symm_snd_fst :
    ((strictIsoEquiv p hlocal).symm f).val.2.1 = f.comp (rightUnit p) ∘ X := (rfl)

@[simp] theorem strictIsoEquiv_symm_snd_snd :
    ((strictIsoEquiv p hlocal).symm f).val.2.2.val =
      FormalCoordinate.map f (universalStrictCoordinate p) := (rfl)

end StrictIsoSimp

section StrictIsoAlg

variable (A : Type*) [CommRing A] [Algebra A R]

/-- **Representability over a `p`-local base ring `A`**: for any commutative ring `A` in which
primes `q ≠ p` are units and any `A`-algebra `R`, `A`-algebra homomorphisms out of
`A[v₁, v₂, …][t₁, t₂, …]` classify all strict Hazewinkel isomorphisms over `R`. -/
def strictIsoAlgEquiv (hlocal : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : A)) :
    {q : (ℕ+ → R) × (ℕ+ → R) × (FormalCoordinate.linearCoeff (R := R)).ker //
      q.2.2.val • hazewinkelIntegralFormalGroup p q.1 = hazewinkelIntegralFormalGroup p q.2.1} ≃
      (MvPolynomial ℕ+ (MvPolynomial ℕ+ A) →ₐ[A] R) :=
  (strictIsoEquiv p fun q hq hqp ↦ by
    simpa only [map_natCast] using (hlocal q hq hqp).map (algebraMap A R)).trans
    (MvPolynomial.iteratedRingHomEquivAlgHom A)

variable (hlocal : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : A))
  (q : {q : (ℕ+ → R) × (ℕ+ → R) × (FormalCoordinate.linearCoeff (R := R)).ker //
    q.2.2.val • hazewinkelIntegralFormalGroup p q.1 = hazewinkelIntegralFormalGroup p q.2.1})
  (g : MvPolynomial ℕ+ (MvPolynomial ℕ+ A) →ₐ[A] R)

@[simp] theorem strictIsoAlgEquiv_C_X (i : ℕ+) :
    strictIsoAlgEquiv p A hlocal q (C (X i)) = q.val.1 i := by simp [strictIsoAlgEquiv]

@[simp] theorem strictIsoAlgEquiv_symm_fst (i : ℕ+) :
    ((strictIsoAlgEquiv p A hlocal).symm g).val.1 i = g (C (X i)) := by simp [strictIsoAlgEquiv]

@[simp] theorem strictIsoAlgEquiv_symm_snd_fst :
    ((strictIsoAlgEquiv p A hlocal).symm g).val.2.1 =
      (g.toRingHom.comp (map (map (Int.castRingHom A)))).comp (rightUnit p) ∘ X := by
  simp [strictIsoAlgEquiv]

@[simp] theorem strictIsoAlgEquiv_symm_snd_snd :
    ((strictIsoAlgEquiv p A hlocal).symm g).val.2.2.val =
      FormalCoordinate.map (g.toRingHom.comp (map (map (Int.castRingHom A))))
        (universalStrictCoordinate p) := by simp [strictIsoAlgEquiv]

variable [IsLocalization.AtPrime A (Ideal.span {(p : ℤ)})]

/-- **Representability of `BP_*BP` over `ℤ_(p)`**: for any localization `A` of `ℤ` at `(p)`,
`A`-algebra homomorphisms out of `A[v₁, v₂, …][t₁, t₂, …]` classify all strict Hazewinkel
isomorphisms over `R`. -/
def strictIsoAlgEquivOfAtPrime :
    {q : (ℕ+ → R) × (ℕ+ → R) × (FormalCoordinate.linearCoeff (R := R)).ker //
      q.2.2.val • hazewinkelIntegralFormalGroup p q.1 = hazewinkelIntegralFormalGroup p q.2.1} ≃
      (MvPolynomial ℕ+ (MvPolynomial ℕ+ A) →ₐ[A] R) :=
  strictIsoAlgEquiv p A fun q hq hqp ↦ by
    simpa only [map_natCast] using
      (IsLocalization.AtPrime.isUnit_to_map_iff A (Ideal.span {(p : ℤ)}) (q : ℤ)).mpr <|
        Ideal.mem_primeCompl_iff.mpr fun hmem ↦ hqp ((Nat.prime_dvd_prime_iff_eq hp.out hq).mp
          (Int.natCast_dvd_natCast.mp (Ideal.mem_span_singleton.mp hmem))).symm

@[simp] theorem strictIsoAlgEquivOfAtPrime_symm_fst (i : ℕ+) :
    ((strictIsoAlgEquivOfAtPrime p A).symm g).val.1 i = g (C (X i)) := by
  simp [strictIsoAlgEquivOfAtPrime]

@[simp] theorem strictIsoAlgEquivOfAtPrime_symm_snd_fst :
    ((strictIsoAlgEquivOfAtPrime p A).symm g).val.2.1 =
      (g.toRingHom.comp (map (map (Int.castRingHom A)))).comp (rightUnit p) ∘ X := by
  simp [strictIsoAlgEquivOfAtPrime]

@[simp] theorem strictIsoAlgEquivOfAtPrime_symm_snd_snd :
    ((strictIsoAlgEquivOfAtPrime p A).symm g).val.2.2.val =
      FormalCoordinate.map (g.toRingHom.comp (map (map (Int.castRingHom A))))
        (universalStrictCoordinate p) := by simp [strictIsoAlgEquivOfAtPrime]

end StrictIsoAlg

section StrictIsoCharP

variable [CharP R p]
  (q : {q : (ℕ+ → R) × (ℕ+ → R) × (FormalCoordinate.linearCoeff (R := R)).ker //
    q.2.2.val • hazewinkelIntegralFormalGroup p q.1 = hazewinkelIntegralFormalGroup p q.2.1})
  (f : MvPolynomial ℕ+ (MvPolynomial ℕ+ ℤ) →+* R)

/-- Over any ring `R` of characteristic `p`, homomorphisms `Γ_p →+* R` classify all strict
isomorphisms between Hazewinkel formal group laws. -/
def strictIsoEquivOfCharP :
    {q : (ℕ+ → R) × (ℕ+ → R) × (FormalCoordinate.linearCoeff (R := R)).ker //
      q.2.2.val • hazewinkelIntegralFormalGroup p q.1 = hazewinkelIntegralFormalGroup p q.2.1} ≃
      (MvPolynomial ℕ+ (MvPolynomial ℕ+ ℤ) →+* R) :=
  strictIsoEquiv p fun _ hq hqp ↦
    (CharP.isUnit_natCast_iff (R := R) hp.out).mpr fun hdvd ↦
      hqp ((Nat.prime_dvd_prime_iff_eq hp.out hq).mp hdvd).symm

@[simp] theorem strictIsoEquivOfCharP_C_X (i : ℕ+) :
    strictIsoEquivOfCharP p q (C (X i)) = q.val.1 i := strictIsoEquiv_C_X p _ q i

theorem strictIsoEquivOfCharP_comp_C_comp_X :
    ⇑((strictIsoEquivOfCharP p q).comp C) ∘ X = q.val.1 := strictIsoEquiv_comp_C_comp_X p _ q

theorem strictIsoEquivOfCharP_comp_rightUnit_comp_X :
    ⇑((strictIsoEquivOfCharP p q).comp (rightUnit p)) ∘ X = q.val.2.1 :=
  strictIsoEquiv_comp_rightUnit_comp_X p _ q

@[simp] theorem strictIsoEquivOfCharP_rightUnit_X (i : ℕ+) :
    strictIsoEquivOfCharP p q (rightUnit p (X i)) = q.val.2.1 i :=
  strictIsoEquiv_rightUnit_X p _ q i

@[simp] theorem map_strictIsoEquivOfCharP_universalStrictCoordinate :
    FormalCoordinate.map (strictIsoEquivOfCharP p q) (universalStrictCoordinate p) =
      q.val.2.2.val :=
  map_strictIsoEquiv_universalStrictCoordinate p _ q

@[simp] theorem strictIsoEquivOfCharP_symm_fst :
    ((strictIsoEquivOfCharP p).symm f).val.1 = f.comp C ∘ X := (rfl)

@[simp] theorem strictIsoEquivOfCharP_symm_snd_fst :
    ((strictIsoEquivOfCharP p).symm f).val.2.1 = f.comp (rightUnit p) ∘ X := (rfl)

@[simp] theorem strictIsoEquivOfCharP_symm_snd_snd :
    ((strictIsoEquivOfCharP p).symm f).val.2.2.val =
      FormalCoordinate.map f (universalStrictCoordinate p) := (rfl)

end StrictIsoCharP

/-! ### The tensor square, coproduct, and conjugation -/

/-- **The universal property of `Γ_p ⊗_V Γ_p`**, modeled as `MvPolynomial ℕ+ Γ_p` via left factor
`C` and right factor `MvPolynomial.map (rightUnit p)`. Instantiates
`MvPolynomial.pushoutEquiv`. -/
def tensorLift :
    {fg : (MvPolynomial ℕ+ (MvPolynomial ℕ+ ℤ) →+* R) ×
        (MvPolynomial ℕ+ (MvPolynomial ℕ+ ℤ) →+* R) //
      fg.1.comp (rightUnit p) = fg.2.comp C} ≃
      (MvPolynomial ℕ+ (MvPolynomial ℕ+ (MvPolynomial ℕ+ ℤ)) →+* R) :=
  MvPolynomial.pushoutEquiv (rightUnit p)

section TensorSimp

variable (fg : {fg : (MvPolynomial ℕ+ (MvPolynomial ℕ+ ℤ) →+* R) ×
    (MvPolynomial ℕ+ (MvPolynomial ℕ+ ℤ) →+* R) // fg.1.comp (rightUnit p) = fg.2.comp C})
  (k k' : MvPolynomial ℕ+ (MvPolynomial ℕ+ (MvPolynomial ℕ+ ℤ)) →+* R)

/-- The left component of `(tensorLift p).symm k` is its restriction along `C`. -/
@[simp] theorem tensorLift_symm_apply_fst : ((tensorLift p).symm k).val.1 = k.comp C :=
  MvPolynomial.pushoutEquiv_symm_apply_fst (rightUnit p) k

/-- The right component of `(tensorLift p).symm k` is its restriction along
`MvPolynomial.map (rightUnit p)`. -/
@[simp] theorem tensorLift_symm_apply_snd :
    ((tensorLift p).symm k).val.2 = k.comp (map (rightUnit p)) :=
  MvPolynomial.pushoutEquiv_symm_apply_snd (rightUnit p) k

/-- `tensorLift p fg` restricts to `fg.val.1` on the left factor `C`. -/
@[simp] theorem tensorLift_comp_C : (tensorLift p fg).comp C = fg.val.1 :=
  MvPolynomial.pushoutEquiv_comp_C (rightUnit p) fg

/-- `tensorLift p fg` restricts to `fg.val.2` on the right factor
`MvPolynomial.map (rightUnit p)`. -/
@[simp] theorem tensorLift_comp_map_rightUnit :
    (tensorLift p fg).comp (map (rightUnit p)) = fg.val.2 :=
  MvPolynomial.pushoutEquiv_comp_map (rightUnit p) fg

/-- `tensorLift p fg` agrees with `fg.val.1` on the left factor. -/
@[simp] theorem tensorLift_C (x : MvPolynomial ℕ+ (MvPolynomial ℕ+ ℤ)) :
    tensorLift p fg (C x) = fg.val.1 x := MvPolynomial.pushoutEquiv_C (rightUnit p) fg x

/-- `tensorLift p fg` agrees with `fg.val.2` on the right factor. -/
@[simp] theorem tensorLift_map_rightUnit (x : MvPolynomial ℕ+ (MvPolynomial ℕ+ ℤ)) :
    tensorLift p fg (map (rightUnit p) x) = fg.val.2 x :=
  MvPolynomial.pushoutEquiv_map (rightUnit p) fg x

/-- `tensorLift p fg` agrees with `fg.val.2` on the generators of the right factor. -/
@[simp] theorem tensorLift_X (i : ℕ+) : tensorLift p fg (X i) = fg.val.2 (X i) :=
  MvPolynomial.pushoutEquiv_X (rightUnit p) fg i

end TensorSimp

/-- A ring homomorphism out of `Γ_p ⊗_V Γ_p` is determined by its restrictions to both factors. -/
theorem tensor_ringHom_ext {k k' : MvPolynomial ℕ+ (MvPolynomial ℕ+ (MvPolynomial ℕ+ ℤ)) →+* R}
    (h₁ : k.comp C = k'.comp C) (h₂ : k.comp (map (rightUnit p)) = k'.comp (map (rightUnit p))) :
    k = k' := MvPolynomial.ringHom_ext_comp_map (rightUnit p) h₁ h₂

private theorem existsUnique_coproduct_params :
    ∃! t : ℕ+ → MvPolynomial ℕ+ (MvPolynomial ℕ+ (MvPolynomial ℕ+ ℤ)),
      FormalCoordinate.map (map (rightUnit p)) (universalStrictCoordinate p) *
          FormalCoordinate.map C (universalStrictCoordinate p) =
        (hazewinkelIntegralFormalGroup p
          (⇑(C.comp (C : MvPolynomial ℕ+ ℤ →+* MvPolynomial ℕ+ (MvPolynomial ℕ+ ℤ))) ∘
            X)).pTypicalStrictCoordinate p t := by
  let R₃ := MvPolynomial ℕ+ (MvPolynomial ℕ+ (MvPolynomial ℕ+ ℤ))
  refine existsUnique_pTypicalStrictCoordinate_eq_of_smul_eq_of_injective p
    (B := MvPolynomial ℕ+ (MvPolynomial ℕ+ (MvPolynomial ℕ+ ℚ)))
    (ι := map (map (map (Int.castRingHom ℚ))))
    (map_injective _ (map_injective _ (map_injective _ Int.cast_injective)))
    (fun q hq _ ↦ by simpa only [map_natCast] using
      (Nat.cast_ne_zero.mpr hq.ne_zero : (q : ℚ) ≠ 0).isUnit.map (algebraMap ℚ _))
    (w := ⇑((map (rightUnit p)).comp (rightUnit p)) ∘ X)
    (MonoidHom.mem_ker.mp (mul_mem (map_universalStrictCoordinate_mem_ker p _)
      (map_universalStrictCoordinate_mem_ker p _))) ?_
  rw [← map_universalHazewinkelIntegralFormalGroup, ← map_universalHazewinkelIntegralFormalGroup,
    mul_smul, ← map_comp_rightUnit (R := R₃) p C, ← map_comp_C (rightUnit p),
    ← map_comp_rightUnit (R := R₃) p (map (rightUnit p))]

/-- The **coproduct** `Δ : Γ_p →+* Γ_p ⊗_V Γ_p`, classifying composition of strict `p`-typical
coordinate changes. -/
def coproduct :
    MvPolynomial ℕ+ (MvPolynomial ℕ+ ℤ) →+*
      MvPolynomial ℕ+ (MvPolynomial ℕ+ (MvPolynomial ℕ+ ℤ)) :=
  MvPolynomial.prodHomEquiv
    (⇑(C.comp (C : MvPolynomial ℕ+ ℤ →+* MvPolynomial ℕ+ (MvPolynomial ℕ+ ℤ))) ∘ X,
      (existsUnique_coproduct_params p).choose)

@[simp] theorem coproduct_comp_C : (coproduct p).comp C = C.comp C := by
  rw [coproduct, MvPolynomial.prodHomEquiv_comp_C]
  exact MvPolynomial.homEquiv.symm_apply_eq.mpr rfl

@[simp] theorem coproduct_C (a : MvPolynomial ℕ+ ℤ) : coproduct p (C a) = C (C a) :=
  RingHom.congr_fun (coproduct_comp_C p) a

/-- Base change of `universalStrictCoordinate p` along `coproduct p` is the composite of the right
and left universal strict coordinates. -/
@[simp] theorem map_coproduct_universalStrictCoordinate :
    FormalCoordinate.map (coproduct p) (universalStrictCoordinate p) =
      FormalCoordinate.map (map (rightUnit p)) (universalStrictCoordinate p) *
        FormalCoordinate.map C (universalStrictCoordinate p) := by
  rw [coproduct, map_prodHomEquiv_universalStrictCoordinate,
    ← (existsUnique_coproduct_params p).choose_spec.left]

theorem map_comp_coproduct_universalStrictCoordinate
    (k : MvPolynomial ℕ+ (MvPolynomial ℕ+ (MvPolynomial ℕ+ ℤ)) →+* R) :
    FormalCoordinate.map (k.comp (coproduct p)) (universalStrictCoordinate p) =
      FormalCoordinate.map (k.comp (map (rightUnit p))) (universalStrictCoordinate p) *
        FormalCoordinate.map (k.comp C) (universalStrictCoordinate p) := by
  simpa only [← FormalCoordinate.map_comp, map_mul] using
    congrArg (FormalCoordinate.map k) (map_coproduct_universalStrictCoordinate p)

theorem comp_coproduct_comp_C (k : MvPolynomial ℕ+ (MvPolynomial ℕ+ (MvPolynomial ℕ+ ℤ)) →+* R) :
    (k.comp (coproduct p)).comp C = (k.comp C).comp C := by
  rw [RingHom.comp_assoc, coproduct_comp_C, RingHom.comp_assoc]

@[simp] theorem coproduct_comp_rightUnit :
    (coproduct p).comp (rightUnit p) = (map (rightUnit p)).comp (rightUnit p) := by
  let R₃ := MvPolynomial ℕ+ (MvPolynomial ℕ+ (MvPolynomial ℕ+ ℤ))
  refine hom_ext (R := R₃) p ?_
  rw [map_comp_rightUnit (R := R₃) p (coproduct p), map_coproduct_universalStrictCoordinate,
    coproduct_comp_C, map_comp_rightUnit (R := R₃) p (map (rightUnit p)), map_comp_C (rightUnit p),
    map_comp_rightUnit (R := R₃) p C, mul_smul]

@[simp] theorem coproduct_rightUnit (a : MvPolynomial ℕ+ ℤ) :
    coproduct p (rightUnit p a) = map (rightUnit p) (rightUnit p a) :=
  RingHom.congr_fun (coproduct_comp_rightUnit p) a

/-- **The left counit law** `(ε ⊗ id) ∘ Δ = id`. -/
theorem tensorLift_counit_id_comp_coproduct :
    (tensorLift p ⟨(C.comp counit, RingHom.id _), by
        rw [RingHom.comp_assoc, counit_comp_rightUnit, RingHom.comp_id, RingHom.id_comp]⟩).comp
          (coproduct p) = RingHom.id (MvPolynomial ℕ+ (MvPolynomial ℕ+ ℤ)) :=
  ringHom_ext_universalStrictCoordinate p
    (by rw [comp_coproduct_comp_C, tensorLift_comp_C, RingHom.comp_assoc, counit_comp_C,
      RingHom.comp_id, RingHom.id_comp])
    (by rw [map_comp_coproduct_universalStrictCoordinate, tensorLift_comp_map_rightUnit,
      tensorLift_comp_C]; simp [FormalCoordinate.map_comp])

/-- **The right counit law** `(id ⊗ ε) ∘ Δ = id`. -/
theorem tensorLift_id_counit_comp_coproduct :
    (tensorLift p ⟨(RingHom.id _, (rightUnit p).comp counit), by
        rw [RingHom.comp_assoc, counit_comp_C, RingHom.comp_id, RingHom.id_comp]⟩).comp
          (coproduct p) = RingHom.id (MvPolynomial ℕ+ (MvPolynomial ℕ+ ℤ)) :=
  ringHom_ext_universalStrictCoordinate p (by rw [comp_coproduct_comp_C, tensorLift_comp_C])
    (by rw [map_comp_coproduct_universalStrictCoordinate, tensorLift_comp_map_rightUnit,
      tensorLift_comp_C]; simp [FormalCoordinate.map_comp])

/-- **Coassociativity for composable triples** of homomorphisms `Γ_p →+* R`. -/
theorem tensorLift_coproduct_assoc {f₁ f₂ f₃ : MvPolynomial ℕ+ (MvPolynomial ℕ+ ℤ) →+* R}
    (h₁₂ : f₁.comp (rightUnit p) = f₂.comp C) (h₂₃ : f₂.comp (rightUnit p) = f₃.comp C) :
    (tensorLift p ⟨((tensorLift p ⟨(f₁, f₂), h₁₂⟩).comp (coproduct p), f₃), by
        rw [RingHom.comp_assoc, coproduct_comp_rightUnit, ← RingHom.comp_assoc,
          tensorLift_comp_map_rightUnit, h₂₃]⟩).comp (coproduct p) =
      (tensorLift p ⟨(f₁, (tensorLift p ⟨(f₂, f₃), h₂₃⟩).comp (coproduct p)), by
        rw [RingHom.comp_assoc, coproduct_comp_C, ← RingHom.comp_assoc,
          tensorLift_comp_C, h₁₂]⟩).comp (coproduct p) :=
  ringHom_ext_universalStrictCoordinate p (by simp only [comp_coproduct_comp_C, tensorLift_comp_C])
    (by simp only [map_comp_coproduct_universalStrictCoordinate, tensorLift_comp_map_rightUnit,
      tensorLift_comp_C, mul_assoc])

/-- **Universal coassociativity** `(Δ ⊗ id) ∘ Δ = (id ⊗ Δ) ∘ Δ` in `Γ_p ⊗_V Γ_p ⊗_V Γ_p`. -/
theorem coproduct_coassoc :
    let ι₁ : MvPolynomial ℕ+ (MvPolynomial ℕ+ ℤ) →+*
        MvPolynomial (ℕ+ ⊕ ℕ+) (MvPolynomial ℕ+ (MvPolynomial ℕ+ ℤ)) := C
    let ι₂ : MvPolynomial ℕ+ (MvPolynomial ℕ+ ℤ) →+*
        MvPolynomial (ℕ+ ⊕ ℕ+) (MvPolynomial ℕ+ (MvPolynomial ℕ+ ℤ)) :=
      eval₂Hom (C.comp (rightUnit p)) (X ∘ Sum.inl)
    let ι₃ : MvPolynomial ℕ+ (MvPolynomial ℕ+ ℤ) →+*
        MvPolynomial (ℕ+ ⊕ ℕ+) (MvPolynomial ℕ+ (MvPolynomial ℕ+ ℤ)) :=
      eval₂Hom (ι₂.comp (rightUnit p)) (X ∘ Sum.inr)
    let h₁₂ : ι₁.comp (rightUnit p) = ι₂.comp C := (RingHom.ext (eval₂Hom_C _ _)).symm
    let h₂₃ : ι₂.comp (rightUnit p) = ι₃.comp C := (RingHom.ext (eval₂Hom_C _ _)).symm
    (tensorLift (R := MvPolynomial (ℕ+ ⊕ ℕ+) (MvPolynomial ℕ+ (MvPolynomial ℕ+ ℤ))) p
      ⟨((tensorLift p ⟨(ι₁, ι₂), h₁₂⟩).comp (coproduct p), ι₃), by
        rw [RingHom.comp_assoc, coproduct_comp_rightUnit, ← RingHom.comp_assoc,
          tensorLift_comp_map_rightUnit, h₂₃]⟩).comp (coproduct p) =
      (tensorLift (R := MvPolynomial (ℕ+ ⊕ ℕ+) (MvPolynomial ℕ+ (MvPolynomial ℕ+ ℤ))) p
        ⟨(ι₁, (tensorLift p ⟨(ι₂, ι₃), h₂₃⟩).comp (coproduct p)), by
        rw [RingHom.comp_assoc, coproduct_comp_C, ← RingHom.comp_assoc, tensorLift_comp_C,
          h₁₂]⟩).comp (coproduct p) :=
  tensorLift_coproduct_assoc p (RingHom.ext (eval₂Hom_C _ _)).symm
    (RingHom.ext (eval₂Hom_C _ _)).symm

private theorem existsUnique_conjugation_params :
    ∃! t : ℕ+ → MvPolynomial ℕ+ (MvPolynomial ℕ+ ℤ),
      (universalStrictCoordinate p)⁻¹ =
        (hazewinkelIntegralFormalGroup p (⇑(rightUnit p) ∘ X)).pTypicalStrictCoordinate p t := by
  refine existsUnique_pTypicalStrictCoordinate_eq_of_smul_eq_of_injective p
    (B := MvPolynomial ℕ+ (MvPolynomial ℕ+ ℚ)) (ι := map (map (Int.castRingHom ℚ)))
    (map_injective _ (map_injective _ Int.cast_injective))
    (fun q hq _ ↦ by simpa only [map_natCast] using
      (Nat.cast_ne_zero.mpr hq.ne_zero : (q : ℚ) ≠ 0).isUnit.map (algebraMap ℚ _))
    (w := C ∘ X) (MonoidHom.mem_ker.mp (inv_mem (universalStrictCoordinate_mem_ker p))) ?_
  rw [← map_universalHazewinkelIntegralFormalGroup, ← map_universalHazewinkelIntegralFormalGroup,
    map_rightUnit, inv_smul_smul]

/-- The **conjugation** `c : Γ_p →+* Γ_p`, classifying the inverse `φ⁻¹ : φ • F_v → F_v`. -/
def conjugation : MvPolynomial ℕ+ (MvPolynomial ℕ+ ℤ) →+* MvPolynomial ℕ+ (MvPolynomial ℕ+ ℤ) :=
  MvPolynomial.prodHomEquiv (⇑(rightUnit p) ∘ X, (existsUnique_conjugation_params p).choose)

@[simp] theorem conjugation_comp_C : (conjugation p).comp C = rightUnit p := by
  rw [conjugation, MvPolynomial.prodHomEquiv_comp_C]
  exact MvPolynomial.homEquiv.symm_apply_eq.mpr rfl

@[simp] theorem conjugation_C (a : MvPolynomial ℕ+ ℤ) : conjugation p (C a) = rightUnit p a :=
  RingHom.congr_fun (conjugation_comp_C p) a

/-- Base change of `universalStrictCoordinate p` along `conjugation p` is its inverse. -/
@[simp] theorem map_conjugation_universalStrictCoordinate :
    FormalCoordinate.map (conjugation p) (universalStrictCoordinate p) =
      (universalStrictCoordinate p)⁻¹ := by
  rw [conjugation, map_prodHomEquiv_universalStrictCoordinate,
    ← (existsUnique_conjugation_params p).choose_spec.left]

@[simp] theorem conjugation_comp_rightUnit : (conjugation p).comp (rightUnit p) = C :=
  hom_ext p <| by
    rw [map_comp_rightUnit, map_conjugation_universalStrictCoordinate, conjugation_comp_C,
      map_rightUnit, inv_smul_smul]

@[simp] theorem conjugation_rightUnit (a : MvPolynomial ℕ+ ℤ) :
    conjugation p (rightUnit p a) = C a := RingHom.congr_fun (conjugation_comp_rightUnit p) a

@[simp] theorem conjugation_comp_conjugation :
    (conjugation p).comp (conjugation p) = RingHom.id _ :=
  ringHom_ext_universalStrictCoordinate p
    (by rw [RingHom.comp_assoc, conjugation_comp_C, conjugation_comp_rightUnit, RingHom.id_comp])
    (by simp [FormalCoordinate.map_comp])

@[simp] theorem conjugation_conjugation (x : MvPolynomial ℕ+ (MvPolynomial ℕ+ ℤ)) :
    conjugation p (conjugation p x) = x := RingHom.congr_fun (conjugation_comp_conjugation p) x

@[simp] theorem counit_comp_conjugation : counit.comp (conjugation p) = counit :=
  ringHom_ext_universalStrictCoordinate p
    (by rw [RingHom.comp_assoc, conjugation_comp_C, counit_comp_rightUnit, counit_comp_C])
    (by simp [FormalCoordinate.map_comp])

@[simp] theorem counit_conjugation (x : MvPolynomial ℕ+ (MvPolynomial ℕ+ ℤ)) :
    counit (conjugation p x) = counit x := RingHom.congr_fun (counit_comp_conjugation p) x

/-- **The left antipode equation** `μ ∘ (c ⊗ id) ∘ Δ = η_R ∘ ε`. -/
theorem tensorLift_conjugation_id_comp_coproduct :
    (tensorLift p ⟨(conjugation p, RingHom.id _), by
        rw [conjugation_comp_rightUnit, RingHom.id_comp]⟩).comp (coproduct p) =
      (rightUnit p).comp counit :=
  ringHom_ext_universalStrictCoordinate p
    (by rw [comp_coproduct_comp_C, tensorLift_comp_C, conjugation_comp_C, RingHom.comp_assoc,
      counit_comp_C, RingHom.comp_id])
    (by rw [map_comp_coproduct_universalStrictCoordinate, tensorLift_comp_map_rightUnit,
      tensorLift_comp_C]; simp [FormalCoordinate.map_comp])

/-- **The right antipode equation** `μ ∘ (id ⊗ c) ∘ Δ = η_L ∘ ε`. -/
theorem tensorLift_id_conjugation_comp_coproduct :
    (tensorLift p ⟨(RingHom.id _, conjugation p), by
        rw [conjugation_comp_C, RingHom.id_comp]⟩).comp (coproduct p) = C.comp counit :=
  ringHom_ext_universalStrictCoordinate p
    (by rw [comp_coproduct_comp_C, tensorLift_comp_C, RingHom.comp_assoc, counit_comp_C,
      RingHom.comp_id, RingHom.id_comp])
    (by rw [map_comp_coproduct_universalStrictCoordinate, tensorLift_comp_map_rightUnit,
      tensorLift_comp_C]; simp [FormalCoordinate.map_comp])

/-! ### Morphism from the Lazard Hopf algebroid `(L, L[b₁, b₂, …])` -/

/-- The canonical ring homomorphism `L →+* ℤ[v₁, v₂, …]` classifying
`universalHazewinkelIntegralFormalGroup p`. -/
def ofLazardRing : LazardRing →+* MvPolynomial ℕ+ ℤ :=
  LazardRing.lift ⟨universalHazewinkelIntegralFormalGroup p, inferInstance⟩

@[simp] theorem map_ofLazardRing :
    LazardRing.formalGroup.map (ofLazardRing p) = universalHazewinkelIntegralFormalGroup p :=
  LazardRing.map_lift _

/-- The canonical ring homomorphism `L[b₁, b₂, …] →+* ℤ[v₁, v₂, …][t₁, t₂, …]` classifying the
universal Hazewinkel formal group law together with `universalStrictCoordinate p`. -/
def ofLazardCoordinateChange :
    MvPolynomial ℕ+ LazardRing →+* MvPolynomial ℕ+ (MvPolynomial ℕ+ ℤ) :=
  LazardRing.coordinateChangeLift
    (⟨(universalHazewinkelIntegralFormalGroup p).map C, inferInstance⟩,
      ⟨universalStrictCoordinate p, universalStrictCoordinate_mem_ker p⟩)

@[simp] theorem map_ofLazardCoordinateChange_universalStrictCoordinate :
    FormalCoordinate.map (ofLazardCoordinateChange p) FormalCoordinate.universalStrictCoordinate =
      universalStrictCoordinate p := LazardRing.map_coordinateChangeLift_universalStrictCoordinate _

@[simp] theorem ofLazardCoordinateChange_comp_C :
    (ofLazardCoordinateChange p).comp C = C.comp (ofLazardRing p) :=
  LazardRing.hom_ext <| by rw [ofLazardCoordinateChange, LazardRing.coordinateChangeLift_comp_C,
    LazardRing.map_lift, ← FormalGroup.map_comp, map_ofLazardRing]

@[simp] theorem ofLazardCoordinateChange_comp_rightUnit :
    (ofLazardCoordinateChange p).comp LazardRing.rightUnit =
      (rightUnit p).comp (ofLazardRing p) :=
  LazardRing.hom_ext <| by
    rw [LazardRing.map_comp_rightUnit, map_ofLazardCoordinateChange_universalStrictCoordinate,
      ofLazardCoordinateChange_comp_C, ← FormalGroup.map_comp, map_ofLazardRing, ← map_rightUnit,
      ← FormalGroup.map_comp, map_ofLazardRing]

@[simp] theorem counit_comp_ofLazardCoordinateChange :
    counit.comp (ofLazardCoordinateChange p) = (ofLazardRing p).comp LazardRing.counit :=
  FormalCoordinate.ringHom_ext_universalStrictCoordinate
    (by rw [RingHom.comp_assoc, ofLazardCoordinateChange_comp_C, ← RingHom.comp_assoc,
      counit_comp_C, RingHom.id_comp, RingHom.comp_assoc, LazardRing.counit_comp_C,
      RingHom.comp_id]) (by simp [FormalCoordinate.map_comp])

/-- `ofLazardCoordinateChange p` commutes with the coproducts of `(L, L[b₁, …])` and `(V, Γ_p)`. -/
theorem coproduct_comp_ofLazardCoordinateChange :
    (coproduct p).comp (ofLazardCoordinateChange p) =
      (LazardRing.tensorLift (R := MvPolynomial ℕ+ (MvPolynomial ℕ+ (MvPolynomial ℕ+ ℤ)))
        ⟨(C.comp (ofLazardCoordinateChange p),
          (map (rightUnit p)).comp (ofLazardCoordinateChange p)), by
            rw [RingHom.comp_assoc, ofLazardCoordinateChange_comp_rightUnit, RingHom.comp_assoc,
              ofLazardCoordinateChange_comp_C, ← RingHom.comp_assoc, ← RingHom.comp_assoc,
              map_comp_C (rightUnit p)]⟩).comp LazardRing.coproduct :=
  FormalCoordinate.ringHom_ext_universalStrictCoordinate
    (R := MvPolynomial ℕ+ (MvPolynomial ℕ+ (MvPolynomial ℕ+ ℤ)))
    (by rw [RingHom.comp_assoc, ofLazardCoordinateChange_comp_C, ← RingHom.comp_assoc,
          coproduct_comp_C, LazardRing.comp_coproduct_comp_C, LazardRing.tensorLift_comp_C]
        dsimp only; rw [RingHom.comp_assoc, RingHom.comp_assoc, ofLazardCoordinateChange_comp_C])
    (by rw [LazardRing.map_comp_coproduct_universalStrictCoordinate,
          LazardRing.tensorLift_comp_map_rightUnit, LazardRing.tensorLift_comp_C]
        simp [FormalCoordinate.map_comp])

@[simp] theorem conjugation_comp_ofLazardCoordinateChange :
    (conjugation p).comp (ofLazardCoordinateChange p) =
      (ofLazardCoordinateChange p).comp LazardRing.conjugation :=
  FormalCoordinate.ringHom_ext_universalStrictCoordinate
    (by rw [RingHom.comp_assoc, ofLazardCoordinateChange_comp_C, ← RingHom.comp_assoc,
      conjugation_comp_C, RingHom.comp_assoc, LazardRing.conjugation_comp_C,
      ofLazardCoordinateChange_comp_rightUnit]) (by simp [FormalCoordinate.map_comp])

/-! ### Ravenel's logarithm recursion, degree-one formulas, and the mod-`(p, v)` quotient -/

/-- **Ravenel's recursion for the right unit** over any `ℚ`-algebra `K`. -/
theorem hazewinkelLogCoeff_comp_rightUnit {K : Type*} [CommRing K] [Algebra ℚ K]
    (f : MvPolynomial ℕ+ (MvPolynomial ℕ+ ℤ) →+* K) (n : ℕ) :
    hazewinkelLogCoeff p (f.comp (rightUnit p) ∘ X) n =
      hazewinkelLogCoeff p (f.comp C ∘ X) n +
        ∑ i ∈ Finset.range n,
          hazewinkelLogCoeff p (f.comp C ∘ X) i * f (X (n - 1 - i).succPNat) ^ p ^ i := by
  have hF := map_comp_rightUnit p f
  simp only [map_universalStrictCoordinate, map_universalHazewinkelIntegralFormalGroup,
    hazewinkelIntegralFormalGroup_eq_hazewinkelFormalGroup] at hF
  have hlog := congrArg (fun G : FormalGroup K ↦ PowerSeries.coeff (p ^ n) G.log) hF
  rwa [log_hazewinkelFormalGroup, coeff_hazewinkelLog_pow _ hp.out.one_lt n,
    log_pTypicalStrictCoordinate_smul_hazewinkelFormalGroup,
    coeff_pow_subst_pTypicalStrictCurve_hazewinkelLog hp.out.one_lt] at hlog

private theorem hazewinkelLogCoeff_comp_rightUnit_of_comp_C_eq_zero {K : Type*} [CommRing K]
    [Algebra ℚ K] {f : MvPolynomial ℕ+ (MvPolynomial ℕ+ ℤ) →+* K}
    (hf0 : ⇑(f.comp C) ∘ X = 0) (n : ℕ) :
    hazewinkelLogCoeff p (f.comp (rightUnit p) ∘ X) (n + 1) = f (X n.succPNat) := by
  rw [hazewinkelLogCoeff_comp_rightUnit, hf0, hazewinkelLogCoeff_zero_succ, zero_add,
    Finset.sum_eq_single 0 (fun i _ hi0 ↦ by
      obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi0
      rw [hazewinkelLogCoeff_zero_succ, zero_mul])
    (fun h0 ↦ absurd (Finset.mem_range.mpr (Nat.succ_pos n)) h0)]
  simp

/-- **`η_R(v₁) = v₁ + p t₁`**. -/
theorem rightUnit_X_one :
    rightUnit p (X 1) = C (X 1) + (p : MvPolynomial ℕ+ (MvPolynomial ℕ+ ℤ)) * X 1 := by
  let ιQ : MvPolynomial ℕ+ (MvPolynomial ℕ+ ℤ) →+* MvPolynomial ℕ+ (MvPolynomial ℕ+ ℚ) :=
    map (map (Int.castRingHom ℚ))
  apply map_injective _ (map_injective (Int.castRingHom ℚ) Int.cast_injective)
  have hrec := hazewinkelLogCoeff_comp_rightUnit p ιQ 1
  have hsucc0 : (0 : ℕ).succPNat = 1 := PNat.eq (Nat.succPNat_coe 0)
  simp only [Finset.range_one, Finset.sum_singleton, hazewinkelLogCoeff_one,
    hazewinkelLogCoeff_zero, Nat.sub_self, hsucc0, pow_zero, pow_one, one_mul, Function.comp_apply,
    RingHom.comp_apply] at hrec
  have hmul := congrArg ((p : ℚ) • ·) hrec
  rw [smul_add, smul_inv_smul₀ (Nat.cast_ne_zero.mpr hp.out.ne_zero),
    smul_inv_smul₀ (Nat.cast_ne_zero.mpr hp.out.ne_zero), Nat.cast_smul_eq_nsmul,
    nsmul_eq_mul] at hmul
  simpa only [ιQ, map_add, map_mul, map_natCast] using hmul

/-- **`Δ(t₁) = t₁ ⊗ 1 + 1 ⊗ t₁`**: `t₁` is primitive in `(V, Γ_p)`. -/
theorem coproduct_X_one : coproduct p (X 1) = C (X 1) + X 1 := by
  apply mul_left_cancel₀ (Nat.cast_ne_zero.mpr hp.out.ne_zero :
    (p : MvPolynomial ℕ+ (MvPolynomial ℕ+ (MvPolynomial ℕ+ ℤ))) ≠ 0)
  have hΔ := congrArg (coproduct p) (rightUnit_X_one p)
  rw [coproduct_rightUnit] at hΔ
  simp only [rightUnit_X_one, coproduct_C, map_add, map_mul, map_natCast, map_C, map_X] at hΔ
  linear_combination -hΔ

/-- **`c(t₁) = -t₁`**: conjugation negates `t₁`. -/
theorem conjugation_X_one : conjugation p (X 1) = -X 1 := by
  apply mul_left_cancel₀ (Nat.cast_ne_zero.mpr hp.out.ne_zero :
    (p : MvPolynomial ℕ+ (MvPolynomial ℕ+ ℤ)) ≠ 0)
  have hc := congrArg (conjugation p) (rightUnit_X_one p)
  rw [conjugation_rightUnit] at hc
  simp only [conjugation_C, rightUnit_X_one, map_add, map_mul, map_natCast] at hc
  linear_combination -hc

private theorem hazewinkelLogCoeff_eval_zero_comp_rightUnit (n : ℕ) :
    hazewinkelLogCoeff p
        (((map (Int.castRingHom ℚ)).comp (map (eval (0 : ℕ+ → ℤ)))).comp (rightUnit p) ∘ X)
        (n + 1) = X n.succPNat := by
  simpa using hazewinkelLogCoeff_comp_rightUnit_of_comp_C_eq_zero p
    (f := (map (Int.castRingHom ℚ)).comp (map (eval (0 : ℕ+ → ℤ)))) (funext fun _ ↦ by simp) n

/-- Modulo `(v₁, v₂, …)`, the right unit `η_R(v_{n + 1})` satisfies
`η_R(v_{n + 1}) + ∑_{i < n} t_{i + 1} η_R(v_{n - i})^(p^(i + 1)) = p t_{n + 1}` in
`ℤ[t₁, t₂, …]`. -/
theorem map_eval_zero_rightUnit_X_succ (n : ℕ) :
    map (eval (0 : ℕ+ → ℤ)) (rightUnit p (X n.succPNat)) +
        ∑ i ∈ Finset.range n, X i.succPNat *
          map (eval (0 : ℕ+ → ℤ)) (rightUnit p (X (n - 1 - i).succPNat)) ^ p ^ (i + 1) =
      (p : MvPolynomial ℕ+ ℤ) * X n.succPNat := by
  apply MvPolynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective
  have hrec := natCast_mul_hazewinkelLogCoeff_succ
    ((((map (Int.castRingHom ℚ)).comp (map (eval (0 : ℕ+ → ℤ)))).comp (rightUnit p)) ∘ X)
    hp.out.ne_zero n
  rw [Finset.sum_range_succ', hazewinkelLogCoeff_eval_zero_comp_rightUnit p n,
    hazewinkelLogCoeff_zero, pow_zero, pow_one, one_mul, Nat.sub_zero, add_comm,
    Finset.sum_congr rfl fun i _ ↦ by
      rw [hazewinkelLogCoeff_eval_zero_comp_rightUnit p i, ← Nat.sub_sub,
        Nat.sub_right_comm]] at hrec
  simpa only [map_add, map_sum, map_mul, map_pow, map_natCast, map_X,
    Function.comp_apply, RingHom.comp_apply] using hrec.symm

/-- Modulo `(v₁, v₂, …)`, `p` divides `η_R(vᵢ)` in `ℤ[t₁, t₂, …]` for every `i`. -/
theorem natCast_dvd_map_eval_zero_rightUnit_X (i : ℕ+) :
    (p : MvPolynomial ℕ+ ℤ) ∣ map (eval (0 : ℕ+ → ℤ)) (rightUnit p (X i)) := by
  induction i using PNat.strongInductionOn with | _ i ih =>
  obtain ⟨n, rfl⟩ : ∃ n, n.succPNat = i := ⟨i.natPred, i.succPNat_natPred⟩
  exact (eq_sub_of_add_eq (map_eval_zero_rightUnit_X_succ p n)) ▸ dvd_sub (dvd_mul_right _ _)
    (Finset.dvd_sum fun k hk ↦ dvd_mul_of_dvd_right (dvd_pow (ih (n - 1 - k).succPNat
      ((PNat.coe_lt_coe _ _).mp (by rw [Finset.mem_range] at hk; simp; omega)))
      (pow_ne_zero _ hp.out.ne_zero)) _)

/-- Modulo `(v₁, v₂, …)`, the coproduct on `t_{n + 1}` reduces in `ℤ[t₁, …] ⊗ ℤ[t₁, …]` to
`t_{n + 1} ⊗ 1 + 1 ⊗ t_{n + 1} + ∑_{i < n} t_{i + 1} ⊗ t_{n - i}^(p^(i + 1))`. -/
theorem map_map_eval_zero_coproduct_X_succ (n : ℕ) :
    map (map (eval (0 : ℕ+ → ℤ))) (coproduct p (X n.succPNat)) =
      C (X n.succPNat) + X n.succPNat +
        ∑ i ∈ Finset.range n, C (X i.succPNat) * X (n - 1 - i).succPNat ^ p ^ (i + 1) := by
  let ev0 : MvPolynomial ℕ+ (MvPolynomial ℕ+ ℤ) →+* MvPolynomial ℕ+ ℤ := map (eval (0 : ℕ+ → ℤ))
  let ιQ : MvPolynomial ℕ+ ℤ →+* MvPolynomial ℕ+ ℚ := map (Int.castRingHom ℚ)
  let CQ : MvPolynomial ℕ+ ℚ →+* MvPolynomial ℕ+ (MvPolynomial ℕ+ ℚ) := C
  let F : MvPolynomial ℕ+ (MvPolynomial ℕ+ (MvPolynomial ℕ+ ℤ)) →+*
      MvPolynomial ℕ+ (MvPolynomial ℕ+ ℚ) := (map ιQ).comp (map ev0)
  apply map_injective (ιQ : MvPolynomial ℕ+ ℤ →+* _) (map_injective _ Int.cast_injective)
  have hA : hazewinkelLogCoeff p ((F.comp (coproduct p)).comp (rightUnit p) ∘ X) (n + 1) =
      map ιQ (map ev0 (coproduct p (X n.succPNat))) := by
    simpa [F] using hazewinkelLogCoeff_comp_rightUnit_of_comp_C_eq_zero p
      (f := F.comp (coproduct p)) (funext fun _ ↦ by simp [F, ev0, ιQ]) n
  have hB : hazewinkelLogCoeff p
      ((F.comp (map (rightUnit p))).comp (rightUnit p) ∘ X) (n + 1) =
      C (X n.succPNat) + X n.succPNat +
        ∑ i ∈ Finset.range n, C (X i.succPNat) * X (n - 1 - i).succPNat ^ p ^ (i + 1) := by
    set w0Q : ℕ+ → MvPolynomial ℕ+ ℚ := ((ιQ.comp ev0).comp (rightUnit p)) ∘ X
    have hFC : ⇑((F.comp (map (rightUnit p))).comp C) ∘ X = CQ ∘ w0Q :=
      funext fun _ ↦ by simp [F, ev0, ιQ, CQ, w0Q]
    have hFX (k : ℕ+) : (F.comp (map (rightUnit p))) (X k) = X k := by simp [F, ev0, ιQ]
    have hterm (k : ℕ) : hazewinkelLogCoeff p (CQ ∘ w0Q) (k + 1) = CQ (X k.succPNat) := by
      rw [← map_hazewinkelLogCoeff w0Q CQ, hazewinkelLogCoeff_eval_zero_comp_rightUnit p k]
    rw [hazewinkelLogCoeff_comp_rightUnit, hFC, hterm n, Finset.sum_range_succ']
    simp only [hazewinkelLogCoeff_zero, hterm, hFX, pow_zero, pow_one, one_mul,
      Nat.add_sub_cancel, Nat.sub_zero, ← Nat.sub_sub, Nat.sub_right_comm, CQ]
    ring
  have hcomp : (F.comp (coproduct p)).comp (rightUnit p) =
      (F.comp (map (rightUnit p))).comp (rightUnit p) := by
    rw [RingHom.comp_assoc, coproduct_comp_rightUnit, ← RingHom.comp_assoc]
  rw [← hA, hcomp, hB]
  simp [ιQ, map_add, map_sum, map_mul, map_pow, map_C, map_X]

/-- **The mod-`(p, v)` quotient homomorphism** `ℤ[v₁, v₂, …][t₁, t₂, …] →+* 𝔽_p[t₁, t₂, …]`
sending `p` and every `vᵢ` to `0` and preserving `tᵢ`.

*Unformalized topological remark (Ravenel, Theorem 4.1.18).* Informally, under `milnorCoproduct`,
`tₙ` corresponds to the conjugate Milnor generator `χ(ξₙ)` (denoted `ζₙ` in Ravenel) inside the
polynomial part `P_* = 𝔽_p[ξ₁, ξ₂, …]` of Milnor's mod-`p` dual Steenrod algebra for odd `p` (or
`𝔽_2[ξ₁, ξ₂, …]` ungraded, and `𝔽_2[ξ₁², ξ₂², …]` via `tₙ ↦ χ(ξₙ)²` in topological grading, at
`p = 2`). -/
def milnorQuotient : MvPolynomial ℕ+ (MvPolynomial ℕ+ ℤ) →+* MvPolynomial ℕ+ (ZMod p) :=
  map ((Int.castRingHom (ZMod p)).comp (eval (0 : ℕ+ → ℤ)))

@[simp] theorem milnorQuotient_X (i : ℕ+) : milnorQuotient p (X i) = X i := by simp [milnorQuotient]

@[simp] theorem milnorQuotient_C_X (i : ℕ+) : milnorQuotient p (C (X i)) = 0 := by
  simp [milnorQuotient]

/-- `milnorQuotient p` is surjective onto `𝔽_p[t₁, t₂, …]`. -/
theorem milnorQuotient_surjective : Function.Surjective (milnorQuotient p) := fun q ↦ by
  obtain ⟨qZ, hqZ⟩ := map_surjective (Int.castRingHom (ZMod p)) ZMod.intCast_surjective q
  refine ⟨map C qZ, by simpa [← RingHom.comp_apply, (ringHom_ext' (RingHom.ext_int _ _) fun _ ↦
    by simp [milnorQuotient] : (milnorQuotient p).comp (map (C : ℤ →+* MvPolynomial ℕ+ ℤ)) =
      map (Int.castRingHom (ZMod p)))] using hqZ⟩

@[simp] theorem milnorQuotient_rightUnit_X (i : ℕ+) : milnorQuotient p (rightUnit p (X i)) = 0 := by
  obtain ⟨u, hu⟩ := natCast_dvd_map_eval_zero_rightUnit_X p i
  rw [milnorQuotient, ← map_map, hu, map_mul, map_natCast, CharP.cast_eq_zero, zero_mul]

@[simp] theorem milnorQuotient_comp_rightUnit :
    (milnorQuotient p).comp (rightUnit p) = (milnorQuotient p).comp C :=
  MvPolynomial.homEquiv.injective <| funext fun _ ↦ by simp [MvPolynomial.homEquiv]

/-- **The ideal `(p, v₁, v₂, …)` is an invariant ideal** of `(V, Γ_p)`. -/
theorem map_rightUnit_ker_eval_zero_mod :
    (RingHom.ker ((Int.castRingHom (ZMod p)).comp (eval (0 : ℕ+ → ℤ)))).map (rightUnit p) =
      (RingHom.ker ((Int.castRingHom (ZMod p)).comp (eval (0 : ℕ+ → ℤ)))).map C := by
  have hle : (RingHom.ker ((Int.castRingHom (ZMod p)).comp (eval (0 : ℕ+ → ℤ)))).map (rightUnit p) ≤
      (RingHom.ker ((Int.castRingHom (ZMod p)).comp (eval (0 : ℕ+ → ℤ)))).map C := by
    rw [← ker_map, ← milnorQuotient, Ideal.map_le_iff_le_comap]; intro a ha
    rw [Ideal.mem_comap, RingHom.mem_ker, ← RingHom.comp_apply (milnorQuotient p),
      milnorQuotient_comp_rightUnit, RingHom.comp_apply, milnorQuotient, map_C,
      RingHom.mem_ker.mp ha, map_zero]
  refine le_antisymm hle ?_
  have h' := Ideal.map_mono (f := conjugation p) hle
  rwa [Ideal.map_map, Ideal.map_map, conjugation_comp_rightUnit, conjugation_comp_C] at h'

/-- **The descended mod-`(p, v)` coproduct** on `𝔽_p[t₁, t₂, …]`
(`milnorCoproduct_comp_milnorQuotient`), given on generators by
`Δ(t_{n + 1}) = t_{n + 1} ⊗ 1 + 1 ⊗ t_{n + 1} + ∑_{i < n} t_{i + 1} ⊗ t_{n - i}^(p^(i + 1))`.

*Unformalized topological remark (Ravenel, Theorem 4.1.18).* Under Milnor's coproduct
`Δ(ξ_k) = ∑_{i = 0}^k ξ_{k - i}^(p^i) ⊗ ξ_i`, this formula agrees with that of the conjugate
generators `ζₙ = χ(ξₙ)` (`tₙ ↦ χ(ξₙ)`, or `tₙ ↦ χ(ξₙ)²` in topological grading at `p = 2`);
mapping `tₙ ↦ ξₙ` instead gives the opposite coproduct. -/
def milnorCoproduct :
    MvPolynomial ℕ+ (ZMod p) →ₐ[ZMod p] MvPolynomial ℕ+ (MvPolynomial ℕ+ (ZMod p)) :=
  MvPolynomial.aeval fun i ↦ C (X i) + X i + ∑ r ∈ Finset.range i.natPred,
    C (X r.succPNat) * X (i.natPred - 1 - r).succPNat ^ p ^ (r + 1)

@[simp] theorem milnorCoproduct_X_succ (n : ℕ) :
    milnorCoproduct p (X n.succPNat) = C (X n.succPNat) + X n.succPNat +
      ∑ r ∈ Finset.range n, C (X r.succPNat) * X (n - 1 - r).succPNat ^ p ^ (r + 1) := by
  simp [milnorCoproduct, Nat.natPred_succPNat]

/-- `coproduct p` descends modulo `(p, v₁, v₂, …)` along `milnorQuotient p` to
`milnorCoproduct p`. -/
theorem milnorCoproduct_comp_milnorQuotient :
    (milnorCoproduct p).toRingHom.comp (milnorQuotient p) =
      (map (milnorQuotient p)).comp (coproduct p) := by
  refine ringHom_ext' (MvPolynomial.homEquiv.injective <| funext fun _ ↦ by
    simp [MvPolynomial.homEquiv]) fun i ↦ ?_
  obtain ⟨n, rfl⟩ : ∃ n, n.succPNat = i := ⟨i.natPred, i.succPNat_natPred⟩
  have hfact : map (milnorQuotient p) (coproduct p (X n.succPNat)) =
      map (map (Int.castRingHom (ZMod p)))
        (map (map (eval (0 : ℕ+ → ℤ))) (coproduct p (X n.succPNat))) := by
    rw [show milnorQuotient p = (map (Int.castRingHom (ZMod p))).comp (map (eval (0 : ℕ+ → ℤ)))
      from RingHom.ext fun q ↦ (map_map _ _ q).symm, ← map_map]
  simp only [RingHom.comp_apply, milnorQuotient_X, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
    milnorCoproduct_X_succ, hfact, map_map_eval_zero_coproduct_X_succ, map_add, map_sum, map_mul,
    map_pow, map_C, map_X]

/-- **The descended mod-`(p, v)` conjugation involution** on `𝔽_p[t₁, t₂, …]`, induced by
`conjugation p` (`milnorConjugation_comp_milnorQuotient`). -/
def milnorConjugation : MvPolynomial ℕ+ (ZMod p) →ₐ[ZMod p] MvPolynomial ℕ+ (ZMod p) :=
  MvPolynomial.aeval fun i ↦ milnorQuotient p (conjugation p (X i))

/-- `milnorConjugation p` sends `X i` to `milnorQuotient p (conjugation p (X i))`. -/
@[simp] theorem milnorConjugation_X_eq (i : ℕ+) :
    milnorConjugation p (X i) = milnorQuotient p (conjugation p (X i)) := aeval_X _ i

/-- `conjugation p` descends modulo `(p, v₁, v₂, …)` along `milnorQuotient p` to
`milnorConjugation p`. -/
theorem milnorConjugation_comp_milnorQuotient :
    (milnorConjugation p).toRingHom.comp (milnorQuotient p) =
      (milnorQuotient p).comp (conjugation p) :=
  ringHom_ext' (MvPolynomial.homEquiv.injective <| funext fun _ ↦ by simp [MvPolynomial.homEquiv])
    fun _ ↦ by simp

/-- `milnorConjugation p` is an involution as an `𝔽_p`-algebra homomorphism. -/
@[simp] theorem milnorConjugation_comp_milnorConjugation :
    (milnorConjugation p).comp (milnorConjugation p) =
      AlgHom.id (ZMod p) (MvPolynomial ℕ+ (ZMod p)) :=
  MvPolynomial.algHom_ext fun i ↦ by
    simpa only [AlgHom.comp_apply, milnorConjugation_X_eq, RingHom.comp_apply,
      AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, conjugation_conjugation, milnorQuotient_X,
      AlgHom.id_apply] using
      RingHom.congr_fun (milnorConjugation_comp_milnorQuotient p) (conjugation p (X i))

/-- `milnorConjugation p` is an involution on elements of `𝔽_p[t₁, t₂, …]`. -/
@[simp] theorem milnorConjugation_conjugation (x : MvPolynomial ℕ+ (ZMod p)) :
    milnorConjugation p (milnorConjugation p x) = x :=
  AlgHom.congr_fun (milnorConjugation_comp_milnorConjugation p) x

/-- **Milnor's recursive conjugation formula** on `𝔽_p[t₁, t₂, …]`:
`c(t_{n + 1}) = -t_{n + 1} - ∑_{i < n} t_{i + 1} c(t_{n - i})^(p^(i + 1))`. -/
theorem milnorConjugation_X_succ (n : ℕ) :
    milnorConjugation p (X n.succPNat) = -X n.succPNat -
      ∑ r ∈ Finset.range n,
        X r.succPNat * milnorConjugation p (X (n - 1 - r).succPNat) ^ p ^ (r + 1) := by
  let μc : MvPolynomial ℕ+ (MvPolynomial ℕ+ (ZMod p)) →+* MvPolynomial ℕ+ (ZMod p) :=
    eval₂Hom (RingHom.id _) (milnorConjugation p ∘ X)
  have hcomm : μc.comp (map (milnorQuotient p)) = (milnorQuotient p).comp
      (tensorLift p ⟨(RingHom.id _, conjugation p),
        by rw [conjugation_comp_C, RingHom.id_comp]⟩) :=
    ringHom_ext' (RingHom.ext fun _ ↦ by simp [μc]) fun _ ↦ by simp [μc]
  have hzero : μc (map (milnorQuotient p) (coproduct p (X n.succPNat))) = 0 := by
    have h1 := RingHom.congr_fun hcomm (coproduct p (X n.succPNat))
    have h2 := congrArg (milnorQuotient p)
      (RingHom.congr_fun (tensorLift_id_conjugation_comp_coproduct p) (X n.succPNat))
    simpa only [RingHom.comp_apply, counit_X, map_zero] using h1.trans h2
  have hcoprod : map (milnorQuotient p) (coproduct p (X n.succPNat)) =
      milnorCoproduct p (X n.succPNat) := by
    simpa only [RingHom.comp_apply, milnorQuotient_X, AlgHom.toRingHom_eq_coe,
      AlgHom.coe_toRingHom] using
      (RingHom.congr_fun (milnorCoproduct_comp_milnorQuotient p) (X n.succPNat)).symm
  rw [hcoprod, milnorCoproduct_X_succ] at hzero
  simp only [μc, map_add, map_sum, map_mul, map_pow, eval₂Hom_C, RingHom.id_apply, eval₂Hom_X',
    Function.comp_apply] at hzero
  linear_combination hzero

end Hazewinkel

end TauCeti
