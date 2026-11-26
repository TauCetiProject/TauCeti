/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.Data.ZMod.Basic
public import TauCeti.Algebra.MvPolynomial.Lift
public import TauCeti.RingTheory.FormalGroup.CoordinateChange.HopfAlgebroid
public import TauCeti.RingTheory.FormalGroup.Hazewinkel.CoordinateChange
import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Tactic.LinearCombination
import TauCeti.Algebra.Algebra.NatCast
import TauCeti.Data.PNat.Basic
import TauCeti.RingTheory.FormalGroup.Hazewinkel.LeadingDifference
import TauCeti.RingTheory.FormalGroup.Hazewinkel.NSMul
import TauCeti.RingTheory.FormalGroup.Logarithm.Basic

/-!
# The Hazewinkel Hopf algebroid of strict `p`-typical coordinate changes

For a prime `p`, let `V = MvPolynomial ℕ+ ℤ = ℤ[v₁, v₂, …]` and
`Γ_p = MvPolynomial ℕ+ V = ℤ[v₁, v₂, …][t₁, t₂, …]`. Homomorphisms `V →+* R` classify
`hazewinkelIntegralFormalGroup p v` (`TauCeti.Hazewinkel.hom_ext`), and `Γ_p →+* R` classifies
`(v, t)` encoding `pTypicalStrictCoordinate p t` via `MvPolynomial.prodHomEquiv`. Integral
invariance and rational descent equip `(V, Γ_p)` with a **Hopf algebroid** structure receiving a
morphism from `(L, L[b₁, b₂, …])`, classifying all strict Hazewinkel isomorphisms when primes
`q ≠ p` are units (`TauCeti.IsLocalization.isUnit_natCast_of_prime_ne`,
`TauCeti.isUnit_natCast_of_prime_ne`), and descending modulo `(p, v₁, v₂, …)` to a Hopf algebra on
`𝔽_p[t₁, t₂, …]`.

*Unformalized topological remark (Ravenel, Theorem 4.1.18; Milnor 1958).* Neither `BP` nor the dual
Steenrod algebra is formalized here; localized at `(p)`, `(V, Γ_p)` is `(V, VT)` (later identified
with `(BP_*, BP_*BP)`), and Milnor's conjugate generators `ζₙ = χ(ξₙ)` satisfy
`Δ(ζ_k) = ∑_{i=0}^k ζ_i ⊗ ζ_{k-i}^(p^i)`, matching `milnorCoproduct` via `tₙ ↦ χ(ξₙ)`
(`tₙ ↦ χ(ξₙ)²` in topological grading at `p = 2`).

## Main definitions and results

* `TauCeti.Hazewinkel.rightUnit`, `TauCeti.Hazewinkel.counit`, `TauCeti.Hazewinkel.tensorLift`,
  `TauCeti.Hazewinkel.coproduct`, `TauCeti.Hazewinkel.conjugation`: Hopf-algebroid maps and laws
  (`counit_comp_C`, `counit_comp_rightUnit`, `coproduct_comp_C`, `coproduct_comp_rightUnit`,
  `tensorLift_counit_id_comp_coproduct`, `tensorLift_id_counit_comp_coproduct`, `coproduct_coassoc`,
  `conjugation_comp_C`, `conjugation_comp_rightUnit`, `conjugation_comp_conjugation`,
  `counit_comp_conjugation`, `tensorLift_conjugation_id_comp_coproduct`,
  `tensorLift_id_conjugation_comp_coproduct`).
* `TauCeti.Hazewinkel.strictIsoEquiv`, `TauCeti.Hazewinkel.strictIsoAlgEquiv`: `p`-local
  classification of strict Hazewinkel isomorphisms.
* `TauCeti.Hazewinkel.ofLazardRing`, `TauCeti.Hazewinkel.ofLazardCoordinateChange`: morphism of
  Hopf algebroids `(L, L[b₁, …]) → (V, Γ_p)`.
* `TauCeti.Hazewinkel.hazewinkelLogCoeff_comp_rightUnit`, `TauCeti.Hazewinkel.rightUnit_X_one`,
  `TauCeti.Hazewinkel.coproduct_X_one`, `TauCeti.Hazewinkel.conjugation_X_one`: Ravenel's recursion
  and degree-one formulas.
* `TauCeti.Hazewinkel.map_rightUnit_ker_eq_map_C`, `TauCeti.Hazewinkel.milnorQuotient`,
  `TauCeti.Hazewinkel.milnorCounit`, `TauCeti.Hazewinkel.milnorCoproduct`,
  `TauCeti.Hazewinkel.milnorConjugation`: invariance of `(p, v₁, …)` and descended Hopf algebra on
  `𝔽_p[t₁, t₂, …]`.

## References

* D. Quillen, *On the formal group laws of unoriented and complex cobordism theory*, 1969.
* J. Milnor, *The Steenrod algebra and its dual*, Ann. of Math. (2) 67 (1958), 150–171.
* [M. Hazewinkel, *Formal Groups and Applications*][hazewinkel1978], Chapter IV.
* D. C. Ravenel, *Complex Cobordism and Stable Homotopy Groups of Spheres*, §4.1 and Appendix A2.1.
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
  exact ringHom_ext' (RingHom.ext_int _ _) (congrFun (hazewinkelIntegralFormalGroup_injective p h))

/-- **The universal `p`-typical strict coordinate** over `ℤ[v₁, v₂, …][t₁, t₂, …]`. -/
def universalStrictCoordinate : FormalCoordinate (MvPolynomial ℕ+ (MvPolynomial ℕ+ ℤ)) :=
  ((universalHazewinkelIntegralFormalGroup p).map C).pTypicalStrictCoordinate p X

/-- `universalStrictCoordinate p` is `pTypicalStrictCoordinate p X` on the universal law. -/
theorem universalStrictCoordinate_def : universalStrictCoordinate p =
    ((universalHazewinkelIntegralFormalGroup p).map C).pTypicalStrictCoordinate p X := (rfl)

/-- The linear coefficient of `universalStrictCoordinate p` is `1`. -/
@[simp] theorem linearCoeff_universalStrictCoordinate :
    FormalCoordinate.linearCoeff (universalStrictCoordinate p) = 1 :=
  FormalGroup.linearCoeff_pTypicalStrictCoordinate _ _ _

/-- `universalStrictCoordinate p` lies in the subgroup of strict coordinates. -/
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

/-- Any base change of `universalStrictCoordinate p` lies in the subgroup of strict coordinates. -/
theorem map_universalStrictCoordinate_mem_ker (f : MvPolynomial ℕ+ (MvPolynomial ℕ+ ℤ) →+* R) :
    FormalCoordinate.map f (universalStrictCoordinate p) ∈
      (FormalCoordinate.linearCoeff (R := R)).ker :=
  map_universalStrictCoordinate p f ▸ FormalGroup.pTypicalStrictCoordinate_mem_ker_linearCoeff _ _ _

/-- A ring homomorphism out of `Γ_p` is uniquely determined by its restriction along `C` and the
base change of `universalStrictCoordinate p` along it. -/
theorem ringHom_ext_universalStrictCoordinate {f g : MvPolynomial ℕ+ (MvPolynomial ℕ+ ℤ) →+* R}
    (hC : f.comp C = g.comp C) (hφ : FormalCoordinate.map f (universalStrictCoordinate p) =
      FormalCoordinate.map g (universalStrictCoordinate p)) : f = g := by
  rw [map_universalStrictCoordinate, map_universalStrictCoordinate, hC] at hφ
  exact ringHom_ext' hC
    (congrFun (FormalGroup.pTypicalStrictCoordinate_injective _ hp.out.one_lt hφ))

/-- Applying `MvPolynomial.prodHomEquiv vt` to `universalStrictCoordinate p` yields
`(hazewinkelIntegralFormalGroup p vt.1).pTypicalStrictCoordinate p vt.2`. -/
@[simp] theorem map_prodHomEquiv_universalStrictCoordinate (vt : (ℕ+ → R) × (ℕ+ → R)) :
    FormalCoordinate.map (MvPolynomial.prodHomEquiv vt) (universalStrictCoordinate p) =
      (hazewinkelIntegralFormalGroup p vt.1).pTypicalStrictCoordinate p vt.2 := by
  have hv : ⇑(MvPolynomial.homEquiv.symm vt.1) ∘ X = vt.1 :=
    funext (MvPolynomial.homEquiv_symm_apply_X vt.1)
  have ht : ⇑(MvPolynomial.prodHomEquiv vt) ∘ X = vt.2 := funext (MvPolynomial.prodHomEquiv_X vt)
  rw [map_universalStrictCoordinate, MvPolynomial.prodHomEquiv_comp_C,
    map_universalHazewinkelIntegralFormalGroup, hv, ht]

/-- The **right unit** `η_R : ℤ[v₁, v₂, …] →+* ℤ[v₁, v₂, …][t₁, t₂, …]`, classifying the target
Hazewinkel formal group law transported along `universalStrictCoordinate p`. -/
def rightUnit : MvPolynomial ℕ+ ℤ →+* MvPolynomial ℕ+ (MvPolynomial ℕ+ ℤ) :=
  homEquiv.symm (existsUnique_pTypicalStrictCoordinate_smul_hazewinkelIntegralFormalGroup p
    (C ∘ (X : ℕ+ → MvPolynomial ℕ+ ℤ)) X).choose

/-- `rightUnit p` classifies the universal Hazewinkel law along `universalStrictCoordinate p`. -/
theorem map_rightUnit : (universalHazewinkelIntegralFormalGroup p).map (rightUnit p) =
    universalStrictCoordinate p • (universalHazewinkelIntegralFormalGroup p).map C := by
  have hX : ⇑(rightUnit p) ∘ X = _ :=
    funext (by rw [rightUnit]; exact MvPolynomial.homEquiv_symm_apply_X _)
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
def counit : MvPolynomial ℕ+ (MvPolynomial ℕ+ ℤ) →+* MvPolynomial ℕ+ ℤ := eval₂Hom (RingHom.id _) 0

/-- The counit kills every coordinate-change generator `X i`. -/
@[simp] theorem counit_X (i : ℕ+) : counit (X i) = 0 := by simp [counit]

/-- `ε η_L = id`: the counit is a left inverse to the left unit `C`. -/
@[simp] theorem counit_comp_C : counit.comp C = RingHom.id (MvPolynomial ℕ+ ℤ) :=
  RingHom.ext (eval₂Hom_C _ _)

/-- The counit restricts to the identity on `ℤ[v₁, v₂, …]`. -/
@[simp] theorem counit_C (a : MvPolynomial ℕ+ ℤ) : counit (C a) = a := eval₂Hom_C _ _ a

end Counit

/-- The counit sends `universalStrictCoordinate p` to the identity coordinate `1`. -/
@[simp] theorem map_counit_universalStrictCoordinate :
    FormalCoordinate.map counit (universalStrictCoordinate p) = 1 := by
  have hc : ⇑counit ∘ X = 0 := funext counit_X
  rw [map_universalStrictCoordinate, counit_comp_C, FormalGroup.map_id, hc,
    FormalGroup.pTypicalStrictCoordinate_zero]

/-- `ε η_R = id`: the counit is a left inverse to `rightUnit p`. -/
@[simp] theorem counit_comp_rightUnit : counit.comp (rightUnit p) = RingHom.id _ := hom_ext p <| by
  rw [map_comp_rightUnit, map_counit_universalStrictCoordinate, counit_comp_C, one_smul]

/-- The counit fixes the image of `rightUnit p` elementwise. -/
@[simp] theorem counit_rightUnit (a : MvPolynomial ℕ+ ℤ) : counit (rightUnit p a) = a :=
  RingHom.congr_fun (counit_comp_rightUnit p) a

/-! ### Full classification of strict isomorphisms over `p`-local rings -/

/-- When primes `q ≠ p` are units in `R` (e.g. in characteristic `p` via
`TauCeti.isUnit_natCast_of_prime_ne`), homomorphisms `Γ_p →+* R` classify all strict isomorphisms
between Hazewinkel formal group laws over `R`. -/
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
    let ex := existsUnique_pTypicalStrictCoordinate_eq_of_smul_eq p hlocal
      (MonoidHom.mem_ker.mp φ.property) hsmul
    let f := MvPolynomial.prodHomEquiv (v, ex.choose)
    have hv : ⇑(f.comp C) ∘ X = v := funext (MvPolynomial.prodHomEquiv_C_X (v, ex.choose))
    have hφ : FormalCoordinate.map f (universalStrictCoordinate p) = φ.val :=
      (map_prodHomEquiv_universalStrictCoordinate p (v, ex.choose)).trans ex.choose_spec.left.symm
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
    dsimp only; rw [ht, ← MvPolynomial.prodHomEquiv_symm_apply_fst f,
      ← MvPolynomial.prodHomEquiv_symm_apply_snd f, Prod.mk.eta]
    exact MvPolynomial.prodHomEquiv.apply_symm_apply f

section StrictIsoSimp
variable (hlocal : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R))
  (q : {q : (ℕ+ → R) × (ℕ+ → R) × (FormalCoordinate.linearCoeff (R := R)).ker //
    q.2.2.val • hazewinkelIntegralFormalGroup p q.1 = hazewinkelIntegralFormalGroup p q.2.1})
  (f : MvPolynomial ℕ+ (MvPolynomial ℕ+ ℤ) →+* R)

/-- `strictIsoEquiv p hlocal q` sends `C (X i)` to the source parameter `q.val.1 i`. -/
@[simp] theorem strictIsoEquiv_C_X (i : ℕ+) :
    strictIsoEquiv p hlocal q (C (X i)) = q.val.1 i := MvPolynomial.prodHomEquiv_C_X _ i

/-- Restricting `strictIsoEquiv p hlocal q` along `C ∘ X` recovers `q.val.1`. -/
theorem strictIsoEquiv_comp_C_comp_X : ⇑((strictIsoEquiv p hlocal q).comp C) ∘ X = q.val.1 :=
  congrArg (fun r ↦ r.val.1) ((strictIsoEquiv p hlocal).symm_apply_apply q)

/-- Restricting `strictIsoEquiv p hlocal q` along `rightUnit p ∘ X` recovers `q.val.2.1`. -/
theorem strictIsoEquiv_comp_rightUnit_comp_X :
    ⇑((strictIsoEquiv p hlocal q).comp (rightUnit p)) ∘ X = q.val.2.1 :=
  congrArg (fun r ↦ r.val.2.1) ((strictIsoEquiv p hlocal).symm_apply_apply q)

/-- `strictIsoEquiv p hlocal q` sends `rightUnit p (X i)` to the target parameter `q.val.2.1 i`. -/
@[simp] theorem strictIsoEquiv_rightUnit_X (i : ℕ+) :
    strictIsoEquiv p hlocal q (rightUnit p (X i)) = q.val.2.1 i :=
  congrFun (strictIsoEquiv_comp_rightUnit_comp_X p hlocal q) i

/-- Mapping `universalStrictCoordinate p` along `strictIsoEquiv p hlocal q` gives `q.val.2.2`. -/
@[simp] theorem map_strictIsoEquiv_universalStrictCoordinate :
    FormalCoordinate.map (strictIsoEquiv p hlocal q) (universalStrictCoordinate p) =
      q.val.2.2.val :=
  congrArg (fun r ↦ r.val.2.2.val) ((strictIsoEquiv p hlocal).symm_apply_apply q)

/-- The source parameters classified by `f : Γ_p →+* R` are `f.comp C ∘ X`. -/
@[simp] theorem strictIsoEquiv_symm_fst : ((strictIsoEquiv p hlocal).symm f).val.1 = f.comp C ∘ X :=
  (rfl)

/-- The target parameters classified by `f : Γ_p →+* R` are `f.comp (rightUnit p) ∘ X`. -/
@[simp] theorem strictIsoEquiv_symm_snd_fst :
    ((strictIsoEquiv p hlocal).symm f).val.2.1 = f.comp (rightUnit p) ∘ X := (rfl)

/-- The strict coordinate classified by `f : Γ_p →+* R` is `map f (universalStrictCoordinate p)`. -/
@[simp] theorem strictIsoEquiv_symm_snd_snd :
    ((strictIsoEquiv p hlocal).symm f).val.2.2.val =
      FormalCoordinate.map f (universalStrictCoordinate p) := (rfl)

end StrictIsoSimp

section StrictIsoAlg
variable (A : Type*) [CommRing A] [Algebra A R]

/-- **Representability over a `p`-local base ring `A`**: when primes `q ≠ p` are units in `A` (e.g.
for a localization of `ℤ` at `(p)` via `TauCeti.IsLocalization.isUnit_natCast_of_prime_ne ℤ p`),
`A`-algebra maps `A[v₁, …][t₁, …] →ₐ[A] R` classify all strict Hazewinkel isomorphisms over `R`. -/
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

/-- `strictIsoAlgEquiv p A hlocal q` sends `C (X i)` to the source parameter `q.val.1 i`. -/
@[simp] theorem strictIsoAlgEquiv_C_X (i : ℕ+) :
    strictIsoAlgEquiv p A hlocal q (C (X i)) = q.val.1 i := by simp [strictIsoAlgEquiv]

/-- `strictIsoAlgEquiv p A hlocal q` sends the base-changed `rightUnit p (X i)` to `q.val.2.1 i`. -/
@[simp] theorem strictIsoAlgEquiv_rightUnit_X (i : ℕ+) :
    strictIsoAlgEquiv p A hlocal q (map (map (Int.castRingHom A)) (rightUnit p (X i))) =
      q.val.2.1 i := by simp [strictIsoAlgEquiv]

/-- Mapping `universalStrictCoordinate p` along `strictIsoAlgEquiv p A hlocal q` gives `q.2.2`. -/
@[simp] theorem map_strictIsoAlgEquiv_universalStrictCoordinate :
    FormalCoordinate.map ((strictIsoAlgEquiv p A hlocal q : _ →+* R).comp
        (map (map (Int.castRingHom A)))) (universalStrictCoordinate p) = q.val.2.2.val := by
  simp [strictIsoAlgEquiv]

/-- Evaluating the source parameters classified by `g : A[v][t] →ₐ[A] R` gives `g (C (X i))`. -/
@[simp] theorem strictIsoAlgEquiv_symm_fst (i : ℕ+) :
    ((strictIsoAlgEquiv p A hlocal).symm g).val.1 i = g (C (X i)) := by simp [strictIsoAlgEquiv]

/-- The target parameters classified by `g : A[v][t] →ₐ[A] R` restrict `g` along `rightUnit p`. -/
@[simp] theorem strictIsoAlgEquiv_symm_snd_fst : ((strictIsoAlgEquiv p A hlocal).symm g).val.2.1 =
    (g.toRingHom.comp (map (map (Int.castRingHom A)))).comp (rightUnit p) ∘ X := by
  simp [strictIsoAlgEquiv]

/-- The strict coordinate classified by `g : A[v][t] →ₐ[A] R` maps `universalStrictCoordinate p`. -/
@[simp] theorem strictIsoAlgEquiv_symm_snd_snd :
    ((strictIsoAlgEquiv p A hlocal).symm g).val.2.2.val = FormalCoordinate.map
      (g.toRingHom.comp (map (map (Int.castRingHom A)))) (universalStrictCoordinate p) := by
  simp [strictIsoAlgEquiv]

end StrictIsoAlg

/-! ### The tensor square, coproduct, and conjugation -/

/-- **The universal property of `Γ_p ⊗_V Γ_p`**, modeled as `MvPolynomial ℕ+ Γ_p` via left factor
`C` and right factor `MvPolynomial.map (rightUnit p)`. Instantiates `MvPolynomial.pushoutEquiv`. -/
abbrev tensorLift :
    {fg : (MvPolynomial ℕ+ (MvPolynomial ℕ+ ℤ) →+* R) ×
        (MvPolynomial ℕ+ (MvPolynomial ℕ+ ℤ) →+* R) // fg.1.comp (rightUnit p) = fg.2.comp C} ≃
      (MvPolynomial ℕ+ (MvPolynomial ℕ+ (MvPolynomial ℕ+ ℤ)) →+* R) :=
  MvPolynomial.pushoutEquiv (rightUnit p)

private theorem existsUnique_coproduct_params :
    ∃! t : ℕ+ → MvPolynomial ℕ+ (MvPolynomial ℕ+ (MvPolynomial ℕ+ ℤ)),
      FormalCoordinate.map (map (rightUnit p)) (universalStrictCoordinate p) *
          FormalCoordinate.map C (universalStrictCoordinate p) =
        (hazewinkelIntegralFormalGroup p (⇑(C.comp
          (C : MvPolynomial ℕ+ ℤ →+* MvPolynomial ℕ+ _)) ∘ X)).pTypicalStrictCoordinate p t := by
  let R₃ := MvPolynomial ℕ+ (MvPolynomial ℕ+ (MvPolynomial ℕ+ ℤ))
  refine existsUnique_pTypicalStrictCoordinate_eq_of_smul_eq_of_injective p
    (B := MvPolynomial ℕ+ (MvPolynomial ℕ+ (MvPolynomial ℕ+ ℚ)))
    (ι := map (map (map (Int.castRingHom ℚ))))
    (map_injective _ (map_injective _ (map_injective _ Int.cast_injective)))
    (fun _ hq _ ↦ isUnit_natCast_of_ne_zero ℚ hq.ne_zero)
    (w := ⇑((map (rightUnit p)).comp (rightUnit p)) ∘ X)
    (MonoidHom.mem_ker.mp (mul_mem (map_universalStrictCoordinate_mem_ker p _)
      (map_universalStrictCoordinate_mem_ker p _))) ?_
  rw [← map_universalHazewinkelIntegralFormalGroup, ← map_universalHazewinkelIntegralFormalGroup,
    mul_smul, ← map_comp_rightUnit (R := R₃) p C, ← map_comp_C (rightUnit p),
    ← map_comp_rightUnit (R := R₃) p (map (rightUnit p))]

/-- The **coproduct** `Δ : Γ_p →+* Γ_p ⊗_V Γ_p`, classifying composition of strict `p`-typical
coordinate changes. -/
def coproduct : MvPolynomial ℕ+ (MvPolynomial ℕ+ ℤ) →+*
    MvPolynomial ℕ+ (MvPolynomial ℕ+ (MvPolynomial ℕ+ ℤ)) :=
  MvPolynomial.prodHomEquiv (⇑(C.comp (C : MvPolynomial ℕ+ ℤ →+* MvPolynomial ℕ+ _)) ∘ X,
    (existsUnique_coproduct_params p).choose)

/-- `Δ η_L = (η_L ⊗ 1) η_L`: the source of a composite is the source of its first factor. -/
@[simp] theorem coproduct_comp_C : (coproduct p).comp C = C.comp C := by
  rw [coproduct, MvPolynomial.prodHomEquiv_comp_C, MvPolynomial.homEquiv.symm_apply_eq,
    MvPolynomial.homEquiv_apply]

/-- `coproduct p` agrees with the left factor inclusion on `V`. -/
@[simp] theorem coproduct_C (a : MvPolynomial ℕ+ ℤ) : coproduct p (C a) = C (C a) :=
  RingHom.congr_fun (coproduct_comp_C p) a

/-- Mapping `universalStrictCoordinate p` along `coproduct p` multiplies right and left copies. -/
@[simp] theorem map_coproduct_universalStrictCoordinate :
    FormalCoordinate.map (coproduct p) (universalStrictCoordinate p) =
      FormalCoordinate.map (map (rightUnit p)) (universalStrictCoordinate p) *
        FormalCoordinate.map C (universalStrictCoordinate p) := by
  rw [coproduct, map_prodHomEquiv_universalStrictCoordinate,
    ← (existsUnique_coproduct_params p).choose_spec.left]

/-- Along `k : Γ_p ⊗_V Γ_p →+* R`, `k ∘ coproduct p` classifies the composite strict coordinate. -/
theorem map_comp_coproduct_universalStrictCoordinate
    (k : MvPolynomial ℕ+ (MvPolynomial ℕ+ (MvPolynomial ℕ+ ℤ)) →+* R) :
    FormalCoordinate.map (k.comp (coproduct p)) (universalStrictCoordinate p) =
      FormalCoordinate.map (k.comp (map (rightUnit p))) (universalStrictCoordinate p) *
        FormalCoordinate.map (k.comp C) (universalStrictCoordinate p) := by
  simpa only [← FormalCoordinate.map_comp, map_mul] using
    congrArg (FormalCoordinate.map k) (map_coproduct_universalStrictCoordinate p)

/-- The source law classified by `k ∘ coproduct p` agrees with the left factor of `k`. -/
theorem comp_coproduct_comp_C (k : MvPolynomial ℕ+ (MvPolynomial ℕ+ (MvPolynomial ℕ+ ℤ)) →+* R) :
    (k.comp (coproduct p)).comp C = (k.comp C).comp C := by
  rw [RingHom.comp_assoc, coproduct_comp_C, RingHom.comp_assoc]

/-- `Δ η_R = (1 ⊗ η_R) η_R`: the target of a composite is the target of its second factor. -/
@[simp] theorem coproduct_comp_rightUnit :
    (coproduct p).comp (rightUnit p) = (map (rightUnit p)).comp (rightUnit p) := by
  let R₃ := MvPolynomial ℕ+ (MvPolynomial ℕ+ (MvPolynomial ℕ+ ℤ))
  refine hom_ext (R := R₃) p ?_
  rw [map_comp_rightUnit (R := R₃) p (coproduct p), map_coproduct_universalStrictCoordinate,
    coproduct_comp_C, map_comp_rightUnit (R := R₃) p (map (rightUnit p)), map_comp_C (rightUnit p),
    map_comp_rightUnit (R := R₃) p C, mul_smul]

/-- `coproduct p` agrees with the right factor on the image of `rightUnit p`. -/
@[simp] theorem coproduct_rightUnit (a : MvPolynomial ℕ+ ℤ) :
    coproduct p (rightUnit p a) = map (rightUnit p) (rightUnit p a) :=
  RingHom.congr_fun (coproduct_comp_rightUnit p) a

/-- **The left counit law** `(ε ⊗ id) ∘ Δ = id`. -/
theorem tensorLift_counit_id_comp_coproduct :
    (tensorLift p ⟨(C.comp counit, RingHom.id _), by
        rw [RingHom.comp_assoc, counit_comp_rightUnit, RingHom.comp_id, RingHom.id_comp]⟩).comp
          (coproduct p) = RingHom.id (MvPolynomial ℕ+ (MvPolynomial ℕ+ ℤ)) :=
  ringHom_ext_universalStrictCoordinate p (by rw [comp_coproduct_comp_C, pushoutEquiv_comp_C,
    RingHom.comp_assoc, counit_comp_C, RingHom.comp_id, RingHom.id_comp]) (by
    rw [map_comp_coproduct_universalStrictCoordinate, pushoutEquiv_comp_map, pushoutEquiv_comp_C]
    simp [FormalCoordinate.map_comp])

/-- **The right counit law** `(id ⊗ ε) ∘ Δ = id`. -/
theorem tensorLift_id_counit_comp_coproduct :
    (tensorLift p ⟨(RingHom.id _, (rightUnit p).comp counit), by
        rw [RingHom.comp_assoc, counit_comp_C, RingHom.comp_id, RingHom.id_comp]⟩).comp
          (coproduct p) = RingHom.id (MvPolynomial ℕ+ (MvPolynomial ℕ+ ℤ)) :=
  ringHom_ext_universalStrictCoordinate p (by rw [comp_coproduct_comp_C, pushoutEquiv_comp_C])
    (by rw [map_comp_coproduct_universalStrictCoordinate, pushoutEquiv_comp_map,
      pushoutEquiv_comp_C]; simp [FormalCoordinate.map_comp])

/-- **Coassociativity for composable triples** of homomorphisms `Γ_p →+* R`. -/
theorem tensorLift_coproduct_assoc {f₁ f₂ f₃ : MvPolynomial ℕ+ (MvPolynomial ℕ+ ℤ) →+* R}
    (h₁₂ : f₁.comp (rightUnit p) = f₂.comp C) (h₂₃ : f₂.comp (rightUnit p) = f₃.comp C) :
    (tensorLift p ⟨((tensorLift p ⟨(f₁, f₂), h₁₂⟩).comp (coproduct p), f₃), by
        rw [RingHom.comp_assoc, coproduct_comp_rightUnit, ← RingHom.comp_assoc,
          pushoutEquiv_comp_map, h₂₃]⟩).comp (coproduct p) =
      (tensorLift p ⟨(f₁, (tensorLift p ⟨(f₂, f₃), h₂₃⟩).comp (coproduct p)), by
        rw [RingHom.comp_assoc, coproduct_comp_C, ← RingHom.comp_assoc,
          pushoutEquiv_comp_C, h₁₂]⟩).comp (coproduct p) :=
  ringHom_ext_universalStrictCoordinate p
    (by simp only [comp_coproduct_comp_C, pushoutEquiv_comp_C])
    (by simp only [map_comp_coproduct_universalStrictCoordinate, pushoutEquiv_comp_map,
      pushoutEquiv_comp_C, mul_assoc])

/-- **Universal coassociativity** `(Δ ⊗ id) ∘ Δ = (id ⊗ Δ) ∘ Δ` in `Γ_p ⊗_V Γ_p ⊗_V Γ_p`. -/
theorem coproduct_coassoc :
    let ι₁ : MvPolynomial ℕ+ (MvPolynomial ℕ+ ℤ) →+*
        MvPolynomial (ℕ+ ⊕ ℕ+) (MvPolynomial ℕ+ (MvPolynomial ℕ+ ℤ)) := C
    let ι₂ := eval₂Hom (ι₁.comp (rightUnit p)) (X ∘ Sum.inl)
    let ι₃ := eval₂Hom (ι₂.comp (rightUnit p)) (X ∘ Sum.inr)
    let h₁₂ : ι₁.comp (rightUnit p) = ι₂.comp C := (RingHom.ext (eval₂Hom_C _ _)).symm
    let h₂₃ : ι₂.comp (rightUnit p) = ι₃.comp C := (RingHom.ext (eval₂Hom_C _ _)).symm
    (tensorLift (R := MvPolynomial (ℕ+ ⊕ ℕ+) (MvPolynomial ℕ+ (MvPolynomial ℕ+ ℤ))) p
      ⟨((tensorLift p ⟨(ι₁, ι₂), h₁₂⟩).comp (coproduct p), ι₃), by
        rw [RingHom.comp_assoc, coproduct_comp_rightUnit, ← RingHom.comp_assoc,
          pushoutEquiv_comp_map, h₂₃]⟩).comp (coproduct p) =
      (tensorLift (R := MvPolynomial (ℕ+ ⊕ ℕ+) (MvPolynomial ℕ+ (MvPolynomial ℕ+ ℤ))) p
        ⟨(ι₁, (tensorLift p ⟨(ι₂, ι₃), h₂₃⟩).comp (coproduct p)), by
        rw [RingHom.comp_assoc, coproduct_comp_C, ← RingHom.comp_assoc, pushoutEquiv_comp_C,
          h₁₂]⟩).comp (coproduct p) :=
  tensorLift_coproduct_assoc p (RingHom.ext (eval₂Hom_C _ _)).symm
    (RingHom.ext (eval₂Hom_C _ _)).symm

private theorem existsUnique_conjugation_params : ∃! t : ℕ+ → MvPolynomial ℕ+ (MvPolynomial ℕ+ ℤ),
    (universalStrictCoordinate p)⁻¹ =
      (hazewinkelIntegralFormalGroup p (⇑(rightUnit p) ∘ X)).pTypicalStrictCoordinate p t := by
  refine existsUnique_pTypicalStrictCoordinate_eq_of_smul_eq_of_injective p
    (B := MvPolynomial ℕ+ (MvPolynomial ℕ+ ℚ)) (ι := map (map (Int.castRingHom ℚ)))
    (map_injective _ (map_injective _ Int.cast_injective))
    (fun _ hq _ ↦ isUnit_natCast_of_ne_zero ℚ hq.ne_zero)
    (w := C ∘ X) (MonoidHom.mem_ker.mp (inv_mem (universalStrictCoordinate_mem_ker p))) ?_
  rw [← map_universalHazewinkelIntegralFormalGroup, ← map_universalHazewinkelIntegralFormalGroup,
    map_rightUnit, inv_smul_smul]

/-- The **conjugation** `c : Γ_p →+* Γ_p`, classifying the inverse `φ⁻¹ : φ • F_v → F_v`. -/
def conjugation : MvPolynomial ℕ+ (MvPolynomial ℕ+ ℤ) →+* MvPolynomial ℕ+ (MvPolynomial ℕ+ ℤ) :=
  MvPolynomial.prodHomEquiv (⇑(rightUnit p) ∘ X, (existsUnique_conjugation_params p).choose)

/-- `c η_L = η_R`: the source of the inverse coordinate change is the target. -/
@[simp] theorem conjugation_comp_C : (conjugation p).comp C = rightUnit p := by
  rw [conjugation, MvPolynomial.prodHomEquiv_comp_C, MvPolynomial.homEquiv.symm_apply_eq,
    MvPolynomial.homEquiv_apply]

/-- `conjugation p` agrees with `rightUnit p` on `V`. -/
@[simp] theorem conjugation_C (a : MvPolynomial ℕ+ ℤ) : conjugation p (C a) = rightUnit p a :=
  RingHom.congr_fun (conjugation_comp_C p) a

/-- Base change of `universalStrictCoordinate p` along `conjugation p` is its inverse. -/
@[simp] theorem map_conjugation_universalStrictCoordinate :
    FormalCoordinate.map (conjugation p) (universalStrictCoordinate p) =
      (universalStrictCoordinate p)⁻¹ := by
  rw [conjugation, map_prodHomEquiv_universalStrictCoordinate,
    ← (existsUnique_conjugation_params p).choose_spec.left]

/-- `c η_R = η_L`: the target of the inverse coordinate change is the source. -/
@[simp] theorem conjugation_comp_rightUnit : (conjugation p).comp (rightUnit p) = C :=
  hom_ext p <| by rw [map_comp_rightUnit, map_conjugation_universalStrictCoordinate,
    conjugation_comp_C, map_rightUnit, inv_smul_smul]

/-- `conjugation p` sends `rightUnit p a` back to `C a`. -/
@[simp] theorem conjugation_rightUnit (a : MvPolynomial ℕ+ ℤ) :
    conjugation p (rightUnit p a) = C a := RingHom.congr_fun (conjugation_comp_rightUnit p) a

/-- `c ∘ c = id`: `conjugation p` is an involution as a ring homomorphism. -/
@[simp] theorem conjugation_comp_conjugation :
    (conjugation p).comp (conjugation p) = RingHom.id _ :=
  ringHom_ext_universalStrictCoordinate p
    (by rw [RingHom.comp_assoc, conjugation_comp_C, conjugation_comp_rightUnit, RingHom.id_comp])
    (by simp [FormalCoordinate.map_comp])

/-- `conjugation p` is an involution on elements of `Γ_p`. -/
@[simp] theorem conjugation_conjugation (x : MvPolynomial ℕ+ (MvPolynomial ℕ+ ℤ)) :
    conjugation p (conjugation p x) = x := RingHom.congr_fun (conjugation_comp_conjugation p) x

/-- `ε ∘ c = ε`: the counit is invariant under `conjugation p`. -/
@[simp] theorem counit_comp_conjugation : counit.comp (conjugation p) = counit :=
  ringHom_ext_universalStrictCoordinate p (by rw [RingHom.comp_assoc, conjugation_comp_C,
    counit_comp_rightUnit, counit_comp_C]) (by simp [FormalCoordinate.map_comp])

/-- Applying `counit` after `conjugation p` equals `counit`. -/
@[simp] theorem counit_conjugation (x : MvPolynomial ℕ+ (MvPolynomial ℕ+ ℤ)) :
    counit (conjugation p x) = counit x := RingHom.congr_fun (counit_comp_conjugation p) x

/-- **The left antipode equation** `μ ∘ (c ⊗ id) ∘ Δ = η_R ∘ ε`. -/
theorem tensorLift_conjugation_id_comp_coproduct :
    (tensorLift p ⟨(conjugation p, RingHom.id _), by
        rw [conjugation_comp_rightUnit, RingHom.id_comp]⟩).comp (coproduct p) =
      (rightUnit p).comp counit :=
  ringHom_ext_universalStrictCoordinate p (by rw [comp_coproduct_comp_C, pushoutEquiv_comp_C,
    conjugation_comp_C, RingHom.comp_assoc, counit_comp_C, RingHom.comp_id]) (by
    rw [map_comp_coproduct_universalStrictCoordinate, pushoutEquiv_comp_map, pushoutEquiv_comp_C]
    simp [FormalCoordinate.map_comp])

/-- **The right antipode equation** `μ ∘ (id ⊗ c) ∘ Δ = η_L ∘ ε`. -/
theorem tensorLift_id_conjugation_comp_coproduct :
    (tensorLift p ⟨(RingHom.id _, conjugation p), by
        rw [conjugation_comp_C, RingHom.id_comp]⟩).comp (coproduct p) = C.comp counit :=
  ringHom_ext_universalStrictCoordinate p (by rw [comp_coproduct_comp_C, pushoutEquiv_comp_C,
    RingHom.comp_assoc, counit_comp_C, RingHom.comp_id, RingHom.id_comp]) (by
    rw [map_comp_coproduct_universalStrictCoordinate, pushoutEquiv_comp_map, pushoutEquiv_comp_C]
    simp [FormalCoordinate.map_comp])

/-! ### Morphism from the Lazard Hopf algebroid `(L, L[b₁, b₂, …])` -/

/-- The canonical ring homomorphism `L →+* ℤ[v₁, v₂, …]` classifying
`universalHazewinkelIntegralFormalGroup p`. -/
def ofLazardRing : LazardRing →+* MvPolynomial ℕ+ ℤ :=
  LazardRing.lift ⟨universalHazewinkelIntegralFormalGroup p, inferInstance⟩

/-- Base change of `LazardRing.formalGroup` along `ofLazardRing p` gives the Hazewinkel law. -/
@[simp] theorem map_ofLazardRing :
    LazardRing.formalGroup.map (ofLazardRing p) = universalHazewinkelIntegralFormalGroup p :=
  LazardRing.map_lift _

/-- The canonical ring homomorphism `L[b₁, b₂, …] →+* ℤ[v₁, v₂, …][t₁, t₂, …]` classifying the
universal Hazewinkel formal group law together with `universalStrictCoordinate p`. -/
def ofLazardCoordinateChange : MvPolynomial ℕ+ LazardRing →+* MvPolynomial ℕ+ (MvPolynomial ℕ+ ℤ) :=
  LazardRing.coordinateChangeLift
    (⟨(universalHazewinkelIntegralFormalGroup p).map C, inferInstance⟩,
      ⟨universalStrictCoordinate p, universalStrictCoordinate_mem_ker p⟩)

/-- `ofLazardCoordinateChange p` maps Lazard's strict coordinate to `universalStrictCoordinate`. -/
@[simp] theorem map_ofLazardCoordinateChange_universalStrictCoordinate :
    FormalCoordinate.map (ofLazardCoordinateChange p) FormalCoordinate.universalStrictCoordinate =
      universalStrictCoordinate p := LazardRing.map_coordinateChangeLift_universalStrictCoordinate _

/-- `ofLazardCoordinateChange p` commutes with the left units `η_L = C`. -/
@[simp] theorem ofLazardCoordinateChange_comp_C :
    (ofLazardCoordinateChange p).comp C = C.comp (ofLazardRing p) :=
  LazardRing.hom_ext <| by rw [ofLazardCoordinateChange, LazardRing.coordinateChangeLift_comp_C,
    LazardRing.map_lift, ← FormalGroup.map_comp, map_ofLazardRing]

/-- `ofLazardCoordinateChange p` commutes with the right units `η_R`. -/
@[simp] theorem ofLazardCoordinateChange_comp_rightUnit :
    (ofLazardCoordinateChange p).comp LazardRing.rightUnit = (rightUnit p).comp (ofLazardRing p) :=
  LazardRing.hom_ext <| by rw [LazardRing.map_comp_rightUnit,
    map_ofLazardCoordinateChange_universalStrictCoordinate, ofLazardCoordinateChange_comp_C,
    ← FormalGroup.map_comp, map_ofLazardRing, ← map_rightUnit, ← FormalGroup.map_comp,
    map_ofLazardRing]

/-- `ofLazardCoordinateChange p` commutes with the counits `ε`. -/
@[simp] theorem counit_comp_ofLazardCoordinateChange :
    counit.comp (ofLazardCoordinateChange p) = (ofLazardRing p).comp LazardRing.counit :=
  FormalCoordinate.ringHom_ext_universalStrictCoordinate (by
    rw [RingHom.comp_assoc, ofLazardCoordinateChange_comp_C, ← RingHom.comp_assoc, counit_comp_C,
      RingHom.id_comp, RingHom.comp_assoc, LazardRing.counit_comp_C, RingHom.comp_id])
    (by simp [FormalCoordinate.map_comp])

/-- `ofLazardCoordinateChange p` commutes with the coproducts of `(L, L[b₁, …])` and `(V, Γ_p)`. -/
theorem coproduct_comp_ofLazardCoordinateChange : (coproduct p).comp (ofLazardCoordinateChange p) =
    (LazardRing.tensorLift (R := MvPolynomial ℕ+ (MvPolynomial ℕ+ (MvPolynomial ℕ+ ℤ)))
      ⟨(C.comp (ofLazardCoordinateChange p),
        (map (rightUnit p)).comp (ofLazardCoordinateChange p)), by
          rw [RingHom.comp_assoc, ofLazardCoordinateChange_comp_rightUnit, RingHom.comp_assoc,
            ofLazardCoordinateChange_comp_C, ← RingHom.comp_assoc, ← RingHom.comp_assoc,
            map_comp_C (rightUnit p)]⟩).comp LazardRing.coproduct :=
  FormalCoordinate.ringHom_ext_universalStrictCoordinate
    (R := MvPolynomial ℕ+ (MvPolynomial ℕ+ (MvPolynomial ℕ+ ℤ)))
    (by rw [RingHom.comp_assoc, ofLazardCoordinateChange_comp_C, ← RingHom.comp_assoc,
          coproduct_comp_C, LazardRing.comp_coproduct_comp_C, pushoutEquiv_comp_C]
        dsimp only; rw [RingHom.comp_assoc, RingHom.comp_assoc, ofLazardCoordinateChange_comp_C])
    (by rw [LazardRing.map_comp_coproduct_universalStrictCoordinate, pushoutEquiv_comp_map,
          pushoutEquiv_comp_C]; simp [FormalCoordinate.map_comp])

/-- `ofLazardCoordinateChange p` commutes with the conjugations `c`. -/
@[simp] theorem conjugation_comp_ofLazardCoordinateChange :
    (conjugation p).comp (ofLazardCoordinateChange p) =
      (ofLazardCoordinateChange p).comp LazardRing.conjugation :=
  FormalCoordinate.ringHom_ext_universalStrictCoordinate
    (by rw [RingHom.comp_assoc, ofLazardCoordinateChange_comp_C, ← RingHom.comp_assoc,
      conjugation_comp_C, RingHom.comp_assoc, LazardRing.conjugation_comp_C,
      ofLazardCoordinateChange_comp_rightUnit]) (by simp [FormalCoordinate.map_comp])

/-! ### Ravenel's logarithm recursion, degree-one formulas, and the mod-`(p, v)` quotient -/

/-- **Ravenel's recursion for the right unit** over any `ℚ`-algebra `K`:
`mₙ(η_R(v)) = mₙ(v) + ∑_{i < n} mᵢ(v) t_{n - i}^(pⁱ)`. -/
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
      obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi0; rw [hazewinkelLogCoeff_zero_succ]; simp)
    (fun h0 ↦ absurd (Finset.mem_range.mpr (Nat.succ_pos n)) h0)]; simp

/-- **`η_R(v₁) = v₁ + p t₁`**. -/
theorem rightUnit_X_one :
    rightUnit p (X 1) = C (X 1) + (p : MvPolynomial ℕ+ (MvPolynomial ℕ+ ℤ)) * X 1 := by
  apply map_injective _ (map_injective (Int.castRingHom ℚ) Int.cast_injective)
  have hrec := hazewinkelLogCoeff_comp_rightUnit p (map (map (Int.castRingHom ℚ))) 1
  have hsucc0 : (0 : ℕ).succPNat = 1 := PNat.eq (Nat.succPNat_coe 0)
  simp only [Finset.range_one, Finset.sum_singleton, hazewinkelLogCoeff_one,
    hazewinkelLogCoeff_zero, Nat.sub_self, hsucc0, pow_zero, pow_one, one_mul, Function.comp_apply,
    RingHom.comp_apply] at hrec
  have hmul := congrArg ((p : ℚ) • ·) hrec
  rw [smul_add, smul_inv_smul₀ (Nat.cast_ne_zero.mpr hp.out.ne_zero),
    smul_inv_smul₀ (Nat.cast_ne_zero.mpr hp.out.ne_zero), Nat.cast_smul_eq_nsmul,
    nsmul_eq_mul] at hmul
  simpa only [map_add, map_mul, map_natCast] using hmul

/-- **`Δ(t₁) = t₁ ⊗ 1 + 1 ⊗ t₁`**: `t₁` is primitive in `(V, Γ_p)`. -/
theorem coproduct_X_one : coproduct p (X 1) = C (X 1) + X 1 := by
  apply mul_left_cancel₀ (Nat.cast_ne_zero.mpr hp.out.ne_zero : (p : MvPolynomial ℕ+ _) ≠ 0)
  have hΔ := (congrArg (coproduct p) (rightUnit_X_one p)).symm.trans (coproduct_rightUnit p (X 1))
  simp only [rightUnit_X_one, coproduct_C, map_add, map_mul, map_natCast, map_C, map_X] at hΔ
  linear_combination hΔ

/-- **`c(t₁) = -t₁`**: conjugation negates `t₁`. -/
theorem conjugation_X_one : conjugation p (X 1) = -X 1 := by
  apply mul_left_cancel₀ (Nat.cast_ne_zero.mpr hp.out.ne_zero : (p : MvPolynomial ℕ+ _) ≠ 0)
  have hc :=
    (congrArg (conjugation p) (rightUnit_X_one p)).symm.trans (conjugation_rightUnit p (X 1))
  simp only [conjugation_C, rightUnit_X_one, map_add, map_mul, map_natCast] at hc
  linear_combination hc

private theorem hazewinkelLogCoeff_eval_zero_comp_rightUnit (n : ℕ) : hazewinkelLogCoeff p
    (((map (Int.castRingHom ℚ)).comp (map (eval (0 : ℕ+ → ℤ)))).comp (rightUnit p) ∘ X)
    (n + 1) = X n.succPNat := by
  simpa using hazewinkelLogCoeff_comp_rightUnit_of_comp_C_eq_zero p
    (f := (map (Int.castRingHom ℚ)).comp (map (eval (0 : ℕ+ → ℤ)))) (funext fun _ ↦ by simp) n

/-- Modulo `(v₁, v₂, …)` in `ℤ[t₁, t₂, …]`,
`η_R(v_{n + 1}) + ∑_{i < n} t_{i + 1} η_R(v_{n - i})^(p^(i + 1)) = p t_{n + 1}`. -/
theorem map_eval_zero_rightUnit_X_succ (n : ℕ) :
    map (eval (0 : ℕ+ → ℤ)) (rightUnit p (X n.succPNat)) +
        ∑ i ∈ Finset.range n, X i.succPNat *
          map (eval (0 : ℕ+ → ℤ)) (rightUnit p (X (n - 1 - i).succPNat)) ^ p ^ (i + 1) =
      (p : MvPolynomial ℕ+ ℤ) * X n.succPNat := by
  apply MvPolynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective
  have hrec := natCast_mul_hazewinkelLogCoeff_succ ((((map (Int.castRingHom ℚ)).comp
    (map (eval (0 : ℕ+ → ℤ)))).comp (rightUnit p)) ∘ X) hp.out.ne_zero n
  rw [Finset.sum_range_succ', hazewinkelLogCoeff_eval_zero_comp_rightUnit p n,
    hazewinkelLogCoeff_zero, pow_zero, pow_one, one_mul, Nat.sub_zero, add_comm,
    Finset.sum_congr rfl fun i _ ↦ by rw [hazewinkelLogCoeff_eval_zero_comp_rightUnit p i,
      ← Nat.sub_sub, Nat.sub_right_comm]] at hrec
  simpa only [map_add, map_sum, map_mul, map_pow, map_natCast, map_X, Function.comp_apply,
    RingHom.comp_apply] using hrec.symm

/-- Modulo `(v₁, v₂, …)`, `p` divides `η_R(vᵢ)` in `ℤ[t₁, t₂, …]` for every `i`. -/
theorem natCast_dvd_map_eval_zero_rightUnit_X (i : ℕ+) :
    (p : MvPolynomial ℕ+ ℤ) ∣ map (eval (0 : ℕ+ → ℤ)) (rightUnit p (X i)) :=
  i.strongInductionOnSuccPNat fun n ih ↦
    (eq_sub_of_add_eq (map_eval_zero_rightUnit_X_succ p n)) ▸ dvd_sub (dvd_mul_right _ _)
      (Finset.dvd_sum fun k hk ↦ dvd_mul_of_dvd_right (dvd_pow (ih (n - 1 - k).succPNat
        (by rw [Finset.mem_range] at hk; simp; omega)) (pow_ne_zero _ hp.out.ne_zero)) _)

/-- Modulo `(v₁, v₂, …)`, `coproduct p (X n.succPNat)` reduces in `ℤ[t₁, …] ⊗ ℤ[t₁, …]` to
`t_{n + 1} ⊗ 1 + 1 ⊗ t_{n + 1} + ∑_{i < n} t_{i + 1} ⊗ t_{n - i}^(p^(i + 1))`. -/
theorem map_map_eval_zero_coproduct_X_succ (n : ℕ) :
    map (map (eval (0 : ℕ+ → ℤ))) (coproduct p (X n.succPNat)) =
      C (X n.succPNat) + X n.succPNat +
        ∑ i ∈ Finset.range n, C (X i.succPNat) * X (n - 1 - i).succPNat ^ p ^ (i + 1) := by
  let ev0 : MvPolynomial ℕ+ (MvPolynomial ℕ+ ℤ) →+* MvPolynomial ℕ+ ℤ := map (eval (0 : ℕ+ → ℤ))
  let ιQ : MvPolynomial ℕ+ ℤ →+* MvPolynomial ℕ+ ℚ := map (Int.castRingHom ℚ)
  let F : MvPolynomial ℕ+ (MvPolynomial ℕ+ (MvPolynomial ℕ+ ℤ)) →+*
      MvPolynomial ℕ+ (MvPolynomial ℕ+ ℚ) := (map ιQ).comp (map ev0)
  apply map_injective (ιQ : MvPolynomial ℕ+ ℤ →+* _) (map_injective _ Int.cast_injective)
  have hA : hazewinkelLogCoeff p ((F.comp (coproduct p)).comp (rightUnit p) ∘ X) (n + 1) =
      map ιQ (map ev0 (coproduct p (X n.succPNat))) := by
    simpa [F] using hazewinkelLogCoeff_comp_rightUnit_of_comp_C_eq_zero p
      (f := F.comp (coproduct p)) (funext fun _ ↦ by simp [F, ev0, ιQ]) n
  set w0Q : ℕ+ → MvPolynomial ℕ+ ℚ := ((ιQ.comp ev0).comp (rightUnit p)) ∘ X
  have hFC : ⇑((F.comp (map (rightUnit p))).comp C) ∘ X =
      (C : _ →+* MvPolynomial ℕ+ _) ∘ w0Q := funext fun _ ↦ by simp [F, ev0, ιQ, w0Q]
  have hterm (k : ℕ) : hazewinkelLogCoeff p ((C : _ →+* MvPolynomial ℕ+ _) ∘ w0Q) (k + 1) =
      C (X k.succPNat) := by
    rw [← map_hazewinkelLogCoeff w0Q C, hazewinkelLogCoeff_eval_zero_comp_rightUnit p k]
  rw [← hA, RingHom.comp_assoc, coproduct_comp_rightUnit, ← RingHom.comp_assoc,
    hazewinkelLogCoeff_comp_rightUnit, hFC, hterm n, Finset.sum_range_succ']
  simp only [hazewinkelLogCoeff_zero, hterm, pow_zero, pow_one, one_mul, Nat.add_sub_cancel,
    Nat.sub_zero, ← Nat.sub_sub, Nat.sub_right_comm, F, ev0, ιQ, map_add, map_sum, map_mul,
    map_pow, map_C, map_X, RingHom.comp_apply]; ring

/-- **The mod-`(p, v)` quotient homomorphism** `ℤ[v₁, v₂, …][t₁, t₂, …] →+* 𝔽_p[t₁, t₂, …]`
sending `p` and every `vᵢ` to `0` and preserving `tᵢ`. -/
def milnorQuotient : MvPolynomial ℕ+ (MvPolynomial ℕ+ ℤ) →+* MvPolynomial ℕ+ (ZMod p) :=
  map ((Int.castRingHom (ZMod p)).comp (eval (0 : ℕ+ → ℤ)))

/-- `milnorQuotient p` preserves each coordinate-change variable `X i`. -/
@[simp] theorem milnorQuotient_X (i : ℕ+) : milnorQuotient p (X i) = X i := by simp [milnorQuotient]

/-- `milnorQuotient p` kills each Hazewinkel generator `C (X i)`. -/
@[simp] theorem milnorQuotient_C_X (i : ℕ+) : milnorQuotient p (C (X i)) = 0 := by
  simp [milnorQuotient]

/-- `milnorQuotient p` is surjective onto `𝔽_p[t₁, t₂, …]`. -/
theorem milnorQuotient_surjective : Function.Surjective (milnorQuotient p) := fun q ↦ by
  obtain ⟨qZ, hqZ⟩ := map_surjective (Int.castRingHom (ZMod p)) ZMod.intCast_surjective q
  have hcomp : (milnorQuotient p).comp (map (C : ℤ →+* MvPolynomial ℕ+ ℤ)) =
      map (Int.castRingHom (ZMod p)) :=
    ringHom_ext' (RingHom.ext_int _ _) fun _ ↦ by simp [milnorQuotient]
  exact ⟨map C qZ, by simpa [← RingHom.comp_apply, hcomp] using hqZ⟩

private theorem algHom_ext_milnorQuotient {B : Type*} [CommSemiring B] [Algebra (ZMod p) B]
    {f g : MvPolynomial ℕ+ (ZMod p) →ₐ[ZMod p] B}
    (h : f.toRingHom.comp (milnorQuotient p) = g.toRingHom.comp (milnorQuotient p)) : f = g :=
  AlgHom.ext fun x ↦ by
    obtain ⟨y, rfl⟩ := milnorQuotient_surjective p x; exact RingHom.congr_fun h y

private theorem toRingHom_comp_eq {A B C : Type*} [CommSemiring A] [CommSemiring B] [CommSemiring C]
    [Algebra (ZMod p) A] [Algebra (ZMod p) B] [Algebra (ZMod p) C]
    (φ₁ : B →ₐ[ZMod p] C) (φ₂ : A →ₐ[ZMod p] B) :
    (φ₁.comp φ₂).toRingHom = φ₁.toRingHom.comp φ₂.toRingHom := RingHom.ext fun _ ↦ rfl

/-- `milnorQuotient p` kills `rightUnit p (X i)` for every `i`. -/
@[simp] theorem milnorQuotient_rightUnit_X (i : ℕ+) : milnorQuotient p (rightUnit p (X i)) = 0 := by
  obtain ⟨u, hu⟩ := natCast_dvd_map_eval_zero_rightUnit_X p i
  rw [milnorQuotient, ← map_map, hu, map_mul, map_natCast, CharP.cast_eq_zero, zero_mul]

/-- `η_R ≡ η_L` modulo `(p, v₁, v₂, …)`: `milnorQuotient p` equalizes `rightUnit p` and `C`. -/
@[simp] theorem milnorQuotient_comp_rightUnit :
    (milnorQuotient p).comp (rightUnit p) = (milnorQuotient p).comp C :=
  ringHom_ext' (RingHom.ext_int _ _) fun _ ↦ by simp

/-- **The ideal `(p, v₁, v₂, …)` is an invariant ideal** of `(V, Γ_p)`: its extensions along
`rightUnit p` and `C` coincide. -/
theorem map_rightUnit_ker_eq_map_C :
    (RingHom.ker ((Int.castRingHom (ZMod p)).comp (eval (0 : ℕ+ → ℤ)))).map (rightUnit p) =
      (RingHom.ker ((Int.castRingHom (ZMod p)).comp (eval (0 : ℕ+ → ℤ)))).map C := by
  let I := RingHom.ker ((Int.castRingHom (ZMod p)).comp (eval (0 : ℕ+ → ℤ)))
  have hle : I.map (rightUnit p) ≤ I.map C := by
    rw [← ker_map, ← milnorQuotient, Ideal.map_le_iff_le_comap]; intro a ha
    rw [Ideal.mem_comap, RingHom.mem_ker, ← RingHom.comp_apply (milnorQuotient p),
      milnorQuotient_comp_rightUnit, RingHom.comp_apply, milnorQuotient, map_C,
      RingHom.mem_ker.mp ha, map_zero]
  exact le_antisymm hle (by simpa only [Ideal.map_map, conjugation_comp_rightUnit,
    conjugation_comp_C] using Ideal.map_mono (f := conjugation p) hle)

/-- **The descended mod-`(p, v)` counit** `ε : 𝔽_p[t₁, t₂, …] →ₐ[𝔽_p] 𝔽_p`, sending `tᵢ ↦ 0`. -/
def milnorCounit : MvPolynomial ℕ+ (ZMod p) →ₐ[ZMod p] ZMod p := MvPolynomial.aeval 0

/-- `milnorCounit p` kills every generator `X i`. -/
@[simp] theorem milnorCounit_X (i : ℕ+) : milnorCounit p (X i) = 0 := aeval_X _ i

/-- `counit` descends modulo `(p, v₁, v₂, …)` along `milnorQuotient p` to `milnorCounit p`. -/
theorem milnorCounit_comp_milnorQuotient :
    (milnorCounit p).toRingHom.comp (milnorQuotient p) =
      ((Int.castRingHom (ZMod p)).comp (eval (0 : ℕ+ → ℤ))).comp counit :=
  ringHom_ext' (ringHom_ext' (RingHom.ext_int _ _) fun _ ↦ by simp) fun _ ↦ by simp

private theorem algebraMap_comp_milnorCounit_comp_milnorQuotient :
    ((Algebra.ofId (ZMod p) (MvPolynomial ℕ+ _)).comp (milnorCounit p)).toRingHom.comp
      (milnorQuotient p) = (milnorQuotient p).comp (C.comp counit) :=
  ringHom_ext' (ringHom_ext' (RingHom.ext_int _ _) fun _ ↦ by simp) fun _ ↦ by simp

/-- **The descended mod-`(p, v)` coproduct** on `𝔽_p[t₁, t₂, …]`
(`milnorCoproduct_comp_milnorQuotient`), given on generators by
`Δ(t_{n + 1}) = t_{n + 1} ⊗ 1 + 1 ⊗ t_{n + 1} + ∑_{i < n} t_{i + 1} ⊗ t_{n - i}^(p^(i + 1))`. -/
def milnorCoproduct :
    MvPolynomial ℕ+ (ZMod p) →ₐ[ZMod p] MvPolynomial ℕ+ (MvPolynomial ℕ+ (ZMod p)) :=
  MvPolynomial.aeval fun i ↦ C (X i) + X i + ∑ r ∈ Finset.range i.natPred,
    C (X r.succPNat) * X (i.natPred - 1 - r).succPNat ^ p ^ (r + 1)

/-- Explicit formula for `milnorCoproduct p` on `X n.succPNat`. -/
@[simp] theorem milnorCoproduct_X_succ (n : ℕ) :
    milnorCoproduct p (X n.succPNat) = C (X n.succPNat) + X n.succPNat +
      ∑ r ∈ Finset.range n, C (X r.succPNat) * X (n - 1 - r).succPNat ^ p ^ (r + 1) := by
  simp [milnorCoproduct, Nat.natPred_succPNat]

/-- `coproduct p` descends modulo `(p, v)` along `milnorQuotient p` to `milnorCoproduct p`. -/
theorem milnorCoproduct_comp_milnorQuotient :
    (milnorCoproduct p).toRingHom.comp (milnorQuotient p) =
      (map (milnorQuotient p)).comp (coproduct p) := by
  refine ringHom_ext' (ringHom_ext' (RingHom.ext_int _ _) fun _ ↦ by simp) fun i ↦ ?_
  rw [← i.succPNat_natPred]
  have hfact : map (milnorQuotient p) (coproduct p (X i.natPred.succPNat)) =
      map (map (Int.castRingHom (ZMod p)))
        (map (map (eval (0 : ℕ+ → ℤ))) (coproduct p (X i.natPred.succPNat))) := by
    rw [show milnorQuotient p = (map (Int.castRingHom (ZMod p))).comp (map (eval (0 : ℕ+ → ℤ)))
      from (RingHom.ext fun q ↦ map_map _ _ q).symm, ← map_map]
  simp only [RingHom.comp_apply, milnorQuotient_X, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
    milnorCoproduct_X_succ, hfact, map_map_eval_zero_coproduct_X_succ, map_add, map_sum, map_mul,
    map_pow, map_C, map_X]

/-- **The left counit law** `(ε ⊗ id) ∘ Δ = id` on `𝔽_p[t₁, t₂, …]`. -/
@[simp] theorem mapAlgHom_milnorCounit_comp_milnorCoproduct :
    (mapAlgHom (milnorCounit p)).comp (milnorCoproduct p) =
      AlgHom.id (ZMod p) (MvPolynomial ℕ+ (ZMod p)) :=
  algHom_ext fun i ↦ by rw [← i.succPNat_natPred, AlgHom.comp_apply, milnorCoproduct_X_succ]; simp

/-- **The right counit law** `(id ⊗ ε) ∘ Δ = id` on `𝔽_p[t₁, t₂, …]`. -/
theorem aevalTower_id_milnorCounit_comp_milnorCoproduct [NeZero p] :
    (aevalTower (AlgHom.id (ZMod p) _) (C ∘ milnorCounit p ∘ X)).comp (milnorCoproduct p) =
      AlgHom.id (ZMod p) (MvPolynomial ℕ+ (ZMod p)) := algHom_ext fun i ↦ by
  rw [← i.succPNat_natPred, AlgHom.comp_apply, milnorCoproduct_X_succ]
  simp [zero_pow (pow_ne_zero _ (NeZero.ne p))]

omit hp in
/-- **Coassociativity** `(Δ ⊗ id) ∘ Δ = (id ⊗ Δ) ∘ Δ` of `milnorCoproduct p`. -/
theorem milnorCoproduct_coassoc [Fact p.Prime] :
    (mapAlgHom (milnorCoproduct p)).comp (milnorCoproduct p) =
      (aevalTower (IsScalarTower.toAlgHom (ZMod p) (MvPolynomial ℕ+ (ZMod p)) _)
        (map (map C) ∘ milnorCoproduct p ∘ X)).comp (milnorCoproduct p) :=
  algHom_ext_milnorQuotient p <| by
    let R₃ := MvPolynomial ℕ+ (MvPolynomial ℕ+ (MvPolynomial ℕ+ (ZMod p)))
    let f₁ : MvPolynomial ℕ+ (MvPolynomial ℕ+ ℤ) →+* R₃ := (C.comp C).comp (milnorQuotient p)
    let f₂ : MvPolynomial ℕ+ (MvPolynomial ℕ+ ℤ) →+* R₃ := (C.comp (map C)).comp (milnorQuotient p)
    let f₃ : MvPolynomial ℕ+ (MvPolynomial ℕ+ ℤ) →+* R₃ := (map (C.comp C)).comp (milnorQuotient p)
    have h₁₂ : f₁.comp (rightUnit p) = f₂.comp C :=
      ringHom_ext' (RingHom.ext_int _ _) fun _ ↦ by simp [f₁, f₂]
    have h₂₃ : f₂.comp (rightUnit p) = f₃.comp C :=
      ringHom_ext' (RingHom.ext_int _ _) fun _ ↦ by simp [f₂, f₃]
    have h₁ : tensorLift (R := R₃) p ⟨(f₁, f₂), h₁₂⟩ =
        (C : _ →+* R₃).comp (map (milnorQuotient p)) :=
      ringHom_ext' (RingHom.ext fun _ ↦ by simp [f₁]) fun _ ↦ by simp [f₂]
    have h₂ : tensorLift (R := R₃) p ⟨(f₂, f₃), h₂₃⟩ =
        (map (map C)).comp (map (milnorQuotient p)) :=
      ringHom_ext' (RingHom.ext fun _ ↦ by simp [f₂]) fun _ ↦ by simp [f₃]
    have hL (h) : tensorLift (R := R₃) p ⟨((tensorLift p ⟨(f₁, f₂), h₁₂⟩).comp (coproduct p), f₃),
          h⟩ = (mapAlgHom (milnorCoproduct p)).toRingHom.comp (map (milnorQuotient p)) :=
      ringHom_ext' (by rw [pushoutEquiv_comp_C]; dsimp only; rw [h₁, RingHom.comp_assoc,
        ← milnorCoproduct_comp_milnorQuotient]; exact RingHom.ext fun _ ↦ by simp)
        fun _ ↦ by simp [f₃]
    have hR (h) : tensorLift (R := R₃) p ⟨(f₁, (tensorLift p ⟨(f₂, f₃), h₂₃⟩).comp (coproduct p)),
          h⟩ = (aevalTower (IsScalarTower.toAlgHom (ZMod p) (MvPolynomial ℕ+ (ZMod p)) _)
            (map (map C) ∘ milnorCoproduct p ∘ X)).toRingHom.comp (map (milnorQuotient p)) :=
      ringHom_ext' (RingHom.ext fun _ ↦ by simp [f₁, algebraMap_eq]) fun i ↦ by
        rw [pushoutEquiv_X]; dsimp only
        have hc := congrArg (map (map (C : _ →+* MvPolynomial ℕ+ _)) : _ → R₃)
          (RingHom.congr_fun (milnorCoproduct_comp_milnorQuotient p) (X i)).symm
        simpa only [RingHom.comp_apply, h₂, milnorQuotient_X, AlgHom.toRingHom_eq_coe,
          AlgHom.coe_toRingHom, map_X, aevalTower_X, Function.comp_apply] using hc
    have hassoc := tensorLift_coproduct_assoc (R := R₃) p h₁₂ h₂₃
    rwa [hL, hR, RingHom.comp_assoc, RingHom.comp_assoc, ← milnorCoproduct_comp_milnorQuotient,
      ← RingHom.comp_assoc, ← RingHom.comp_assoc, ← toRingHom_comp_eq, ← toRingHom_comp_eq]
      at hassoc

/-- **The descended mod-`(p, v)` conjugation** on `𝔽_p[t₁, t₂, …]` (`milnorConjugation_X_succ`). -/
def milnorConjugation : MvPolynomial ℕ+ (ZMod p) →ₐ[ZMod p] MvPolynomial ℕ+ (ZMod p) :=
  MvPolynomial.aeval fun i ↦ milnorQuotient p (conjugation p (X i))

/-- `milnorConjugation p` sends `X i` to `milnorQuotient p (conjugation p (X i))`. -/
theorem milnorConjugation_X (i : ℕ+) :
    milnorConjugation p (X i) = milnorQuotient p (conjugation p (X i)) := aeval_X _ i

/-- `conjugation p` descends modulo `(p, v)` along `milnorQuotient p` to `milnorConjugation p`. -/
theorem milnorConjugation_comp_milnorQuotient : (milnorConjugation p).toRingHom.comp
    (milnorQuotient p) = (milnorQuotient p).comp (conjugation p) :=
  ringHom_ext' (ringHom_ext' (RingHom.ext_int _ _) fun _ ↦ by simp) fun _ ↦ by
    simp [milnorConjugation_X]

/-- `milnorConjugation p` is an involution as an `𝔽_p`-algebra homomorphism. -/
@[simp] theorem milnorConjugation_comp_milnorConjugation :
    (milnorConjugation p).comp (milnorConjugation p) =
      AlgHom.id (ZMod p) (MvPolynomial ℕ+ (ZMod p)) := MvPolynomial.algHom_ext fun i ↦ by
  simpa only [AlgHom.comp_apply, milnorConjugation_X, RingHom.comp_apply, AlgHom.toRingHom_eq_coe,
    AlgHom.coe_toRingHom, conjugation_conjugation, milnorQuotient_X, AlgHom.id_apply] using
    RingHom.congr_fun (milnorConjugation_comp_milnorQuotient p) (conjugation p (X i))

/-- `milnorConjugation p` is an involution on elements of `𝔽_p[t₁, t₂, …]`. -/
@[simp] theorem milnorConjugation_milnorConjugation (x : MvPolynomial ℕ+ (ZMod p)) :
    milnorConjugation p (milnorConjugation p x) = x :=
  AlgHom.congr_fun (milnorConjugation_comp_milnorConjugation p) x

/-- `milnorCounit p` is invariant under `milnorConjugation p`. -/
@[simp] theorem milnorCounit_comp_milnorConjugation :
    (milnorCounit p).comp (milnorConjugation p) = milnorCounit p :=
  algHom_ext_milnorQuotient p <| by rw [toRingHom_comp_eq, RingHom.comp_assoc,
    milnorConjugation_comp_milnorQuotient, ← RingHom.comp_assoc, milnorCounit_comp_milnorQuotient,
    RingHom.comp_assoc, counit_comp_conjugation]

/-- **The left antipode equation** `μ ∘ (c ⊗ id) ∘ Δ = η ∘ ε` on `𝔽_p[t₁, t₂, …]`. -/
theorem aevalTower_milnorConjugation_id_comp_milnorCoproduct :
    (aevalTower (milnorConjugation p) X).comp (milnorCoproduct p) =
      (Algebra.ofId (ZMod p) _).comp (milnorCounit p) := algHom_ext_milnorQuotient p <| by
  have hcomm (h) : (aevalTower (milnorConjugation p) X).toRingHom.comp (map (milnorQuotient p)) =
      (milnorQuotient p).comp (tensorLift p ⟨(conjugation p, RingHom.id _), h⟩) :=
    ringHom_ext' (RingHom.ext fun x ↦ by
      simpa using RingHom.congr_fun (milnorConjugation_comp_milnorQuotient p) x) fun _ ↦ by simp
  rw [toRingHom_comp_eq, RingHom.comp_assoc, milnorCoproduct_comp_milnorQuotient,
    ← RingHom.comp_assoc, hcomm (by rw [conjugation_comp_rightUnit, RingHom.id_comp]),
    RingHom.comp_assoc, tensorLift_conjugation_id_comp_coproduct, ← RingHom.comp_assoc,
    milnorQuotient_comp_rightUnit, RingHom.comp_assoc,
    algebraMap_comp_milnorCounit_comp_milnorQuotient]

/-- **The right antipode equation** `μ ∘ (id ⊗ c) ∘ Δ = η ∘ ε` on `𝔽_p[t₁, t₂, …]`. -/
theorem aevalTower_id_milnorConjugation_comp_milnorCoproduct :
    (aevalTower (AlgHom.id (ZMod p) _) (milnorConjugation p ∘ X)).comp (milnorCoproduct p) =
      (Algebra.ofId (ZMod p) _).comp (milnorCounit p) := algHom_ext_milnorQuotient p <| by
  have hcomm (h) : (aevalTower (AlgHom.id (ZMod p) _)
      (milnorConjugation p ∘ X)).toRingHom.comp (map (milnorQuotient p)) =
      (milnorQuotient p).comp (tensorLift p ⟨(RingHom.id _, conjugation p), h⟩) :=
    ringHom_ext' (RingHom.ext fun _ ↦ by simp) fun _ ↦ by simp [milnorConjugation_X]
  rw [toRingHom_comp_eq, RingHom.comp_assoc, milnorCoproduct_comp_milnorQuotient,
    ← RingHom.comp_assoc, hcomm (by rw [conjugation_comp_C, RingHom.id_comp]), RingHom.comp_assoc,
    tensorLift_id_conjugation_comp_coproduct, algebraMap_comp_milnorCounit_comp_milnorQuotient]

/-- **Milnor's recursive conjugation formula** on `𝔽_p[t₁, t₂, …]`:
`c(t_{n + 1}) = -t_{n + 1} - ∑_{i < n} t_{i + 1} c(t_{n - i})^(p^(i + 1))`. -/
theorem milnorConjugation_X_succ (n : ℕ) : milnorConjugation p (X n.succPNat) = -X n.succPNat -
      ∑ r ∈ Finset.range n,
        X r.succPNat * milnorConjugation p (X (n - 1 - r).succPNat) ^ p ^ (r + 1) := by
  have h := AlgHom.congr_fun (aevalTower_id_milnorConjugation_comp_milnorCoproduct p) (X n.succPNat)
  simp only [AlgHom.comp_apply, milnorCoproduct_X_succ, milnorCounit_X, map_zero, map_add,
    map_sum, map_mul, map_pow, aevalTower_C, AlgHom.id_apply, aevalTower_X,
    Function.comp_apply] at h; linear_combination h

end Hazewinkel

end TauCeti
