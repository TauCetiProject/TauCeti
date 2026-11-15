/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.Algebra.MvPolynomial.Monad
public import Mathlib.Data.ZMod.Basic
public import Mathlib.RingTheory.Ideal.Int
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import TauCeti.RingTheory.FormalGroup.CoordinateChange.HopfAlgebroid
public import TauCeti.RingTheory.FormalGroup.Hazewinkel.CoordinateChange
import Mathlib.Tactic.LinearCombination
import TauCeti.RingTheory.FormalGroup.Logarithm.Basic

/-!
# The Hazewinkel and Brown–Peterson Hopf algebroid of strict `p`-typical coordinate changes

Fix a prime `p`. Write `V = ℤ[v₁, v₂, …] = MvPolynomial ℕ+ ℤ` and
`Γ_p = V[t₁, t₂, …] = MvPolynomial ℕ+ V`. Ring homomorphisms `V →+* R` classify sequences
`v : ℕ+ → R` and hence Hazewinkel formal group laws `hazewinkelIntegralFormalGroup p v` over `R`
(`TauCeti.Hazewinkel.hom_ext`), while ring homomorphisms `Γ_p →+* R` classify pairs `(v, t)` of
sequences in `R`, encoding the strict `p`-typical coordinate change
`φ_{v, t} = (hazewinkelIntegralFormalGroup p v).pTypicalStrictCoordinate p t`
(`TauCeti.Hazewinkel.coordinateChangeLift`).

Because transporting `hazewinkelIntegralFormalGroup p v` along `pTypicalStrictCoordinate p t`
produces a unique `hazewinkelIntegralFormalGroup p w` over every commutative ring, and because any
composite or inverse of universal `p`-typical strict coordinates descends from `ℚ`-coefficients to
`ℤ`-coefficients, the pair `(V, Γ_p)` carries a canonical integral **Hopf algebroid** structure:

* the **left unit** `η_L = C : V →+* Γ_p`, classifying the source `F_v`;
* the **right unit** `η_R : V →+* Γ_p` (`TauCeti.Hazewinkel.rightUnit`), classifying the target
  `φ_{v, t} • F_v`;
* the **counit** `ε : Γ_p →+* V` (`TauCeti.Hazewinkel.counit`), sending `tᵢ ↦ 0` and classifying the
  identity coordinate;
* the **coproduct** `Δ : Γ_p →+* Γ_p ⊗_V Γ_p = MvPolynomial ℕ+ Γ_p`
  (`TauCeti.Hazewinkel.coproduct`), classifying composition of strict `p`-typical coordinate
  changes;
* the **conjugation** `c : Γ_p →+* Γ_p` (`TauCeti.Hazewinkel.conjugation`), classifying inversion.

Over any commutative ring `R` in which every prime `q ≠ p` is invertible — in particular over any
`ℤ_(p)`-algebra or `𝔽_p`-algebra — *every* strict isomorphism between Hazewinkel formal group laws
is `p`-typical (`TauCeti.existsUnique_pTypicalStrictCoordinate_eq_of_smul_eq`). Extending scalars to
any localization `A` of `ℤ` at `(p)` therefore identifies `BP_* = A[v₁, v₂, …]` and
`BP_*BP = BP_*[t₁, t₂, …]` with the Hopf algebroid corepresenting the full groupoid of Hazewinkel
formal group laws and all strict isomorphisms between them (`TauCeti.Hazewinkel.strictIsoEquiv`,
`TauCeti.Hazewinkel.strictIsoAlgEquiv`, `TauCeti.Hazewinkel.strictIsoEquivOfCharP`).

Following the cogroupoid model of `TauCeti.LazardRing` in
`TauCeti.RingTheory.FormalGroup.CoordinateChange.HopfAlgebroid`, we model the pushout
`Γ_p ⊗_V Γ_p` as `MvPolynomial ℕ+ Γ_p` (`TauCeti.Hazewinkel.tensorLift`) and construct the
canonical Hopf algebroid morphism `(L, L[b₁, b₂, …]) → (V, Γ_p)` from the Lazard Hopf algebroid
(`TauCeti.Hazewinkel.ofLazardRing`, `TauCeti.Hazewinkel.ofLazardCoordinateChange`). Finally, we
prove Ravenel's rational logarithm recursion for `η_R` and the degree-one formulas
`η_R(v₁) = v₁ + p t₁`, `Δ(t₁) = t₁ ⊗ 1 + 1 ⊗ t₁`, and `c(t₁) = -t₁`, and show that killing
`(p, v₁, v₂, …)` projects `(V, Γ_p)` onto Milnor's polynomial dual Steenrod algebra
`𝔽_p[t₁, t₂, …]` with coproduct
`Δ(tₙ) = tₙ ⊗ 1 + 1 ⊗ tₙ + ∑_{1 ≤ i < n} tᵢ ⊗ t_{n - i}^(pⁱ)` and recursive antipode
`c(tₙ) = -tₙ - ∑_{1 ≤ i < n} tᵢ c(t_{n - i})^(pⁱ)`.

## Main definitions

* `TauCeti.Hazewinkel.universalStrictCoordinate`: the universal `p`-typical strict coordinate over
  `ℤ[v₁, v₂, …][t₁, t₂, …]`.
* `TauCeti.Hazewinkel.coordinateChangeLift`: the bijection between pairs `(v, t)` in `R` and ring
  homomorphisms `ℤ[v₁, v₂, …][t₁, t₂, …] →+* R`.
* `TauCeti.Hazewinkel.rightUnit`, `TauCeti.Hazewinkel.counit`, `TauCeti.Hazewinkel.tensorLift`,
  `TauCeti.Hazewinkel.coproduct`, `TauCeti.Hazewinkel.conjugation`: the Hopf algebroid structure
  maps on `(ℤ[v₁, v₂, …], ℤ[v₁, v₂, …][t₁, t₂, …])`.
* `TauCeti.Hazewinkel.strictIsoEquiv`, `TauCeti.Hazewinkel.strictIsoAlgEquiv`,
  `TauCeti.Hazewinkel.strictIsoEquivOfCharP`: classification of all strict isomorphisms between
  Hazewinkel formal group laws over `p`-local rings, `ℤ_(p)`-algebras, and `𝔽_p`-algebras.
* `TauCeti.Hazewinkel.ofLazardRing`, `TauCeti.Hazewinkel.ofLazardCoordinateChange`: the morphism of
  Hopf algebroids from `(L, L[b₁, b₂, …])`.
* `TauCeti.Hazewinkel.milnorQuotient`, `TauCeti.Hazewinkel.milnorCoproduct`,
  `TauCeti.Hazewinkel.milnorConjugation`: the reduction modulo `(p, v₁, v₂, …)` to Milnor's
  polynomial dual Steenrod algebra `𝔽_p[t₁, t₂, …]`.

## Main results

* `TauCeti.Hazewinkel.coproduct_comp_C`, `TauCeti.Hazewinkel.coproduct_comp_rightUnit`,
  `TauCeti.Hazewinkel.tensorLift_counit_id_comp_coproduct`,
  `TauCeti.Hazewinkel.tensorLift_id_counit_comp_coproduct`,
  `TauCeti.Hazewinkel.tensorLift_coproduct_assoc`, `TauCeti.Hazewinkel.coproduct_coassoc`:
  unit, counit, and coassociativity laws of the coproduct.
* `TauCeti.Hazewinkel.conjugation_comp_C`, `TauCeti.Hazewinkel.conjugation_comp_rightUnit`,
  `TauCeti.Hazewinkel.conjugation_comp_conjugation`, `TauCeti.Hazewinkel.counit_comp_conjugation`,
  `TauCeti.Hazewinkel.tensorLift_conjugation_id_comp_coproduct`,
  `TauCeti.Hazewinkel.tensorLift_id_conjugation_comp_coproduct`: unit, involution, counit, and
  antipode laws of the conjugation.
* `TauCeti.Hazewinkel.hazewinkelLogCoeff_comp_rightUnit`, `TauCeti.Hazewinkel.rightUnit_X_one`,
  `TauCeti.Hazewinkel.coproduct_X_one`, `TauCeti.Hazewinkel.conjugation_X_one`: Ravenel's logarithm
  recursion for `η_R` and explicit formulas on `v₁` and `t₁`.
* `TauCeti.Hazewinkel.milnorQuotient_comp_rightUnit`,
  `TauCeti.Hazewinkel.milnorCoproduct_comp_milnorQuotient`,
  `TauCeti.Hazewinkel.milnorConjugation_comp_milnorQuotient`,
  `TauCeti.Hazewinkel.milnorConjugation_X_succ`: descent to `𝔽_p[t₁, t₂, …]` and Milnor's coproduct
  and antipode formulas.

## References

* D. Quillen, *On the formal group laws of unoriented and complex cobordism theory*,
  Bull. Amer. Math. Soc. 75 (1969), 1293–1298.
* J. Milnor, *The Steenrod algebra and its dual*, Ann. of Math. (2) 67 (1958), 150–171.
* [M. Hazewinkel, *Formal Groups and Applications*][hazewinkel1978], Chapter IV.
* D. C. Ravenel, *Complex Cobordism and Stable Homotopy Groups of Spheres*, Section 4.1 and
  Appendix A2.1 (Theorem A2.1.27).
-/

public section

noncomputable section

open MvPolynomial

namespace TauCeti

namespace Hazewinkel

variable {R : Type*} [CommRing R] (p : ℕ) [hp : Fact p.Prime]

/-! ### Representability of Hazewinkel laws and `p`-typical strict coordinates -/

/-- A ring homomorphism out of `ℤ[v₁, v₂, …]` is uniquely determined by the base change of
`universalHazewinkelIntegralFormalGroup p` along it, over any commutative ring `R`. -/
theorem hom_ext {f g : MvPolynomial ℕ+ ℤ →+* R}
    (h : (universalHazewinkelIntegralFormalGroup p).map f =
      (universalHazewinkelIntegralFormalGroup p).map g) :
    f = g := by
  rw [map_universalHazewinkelIntegralFormalGroup, map_universalHazewinkelIntegralFormalGroup] at h
  exact MvPolynomial.homEquiv.injective (hazewinkelIntegralFormalGroup_injective p h)

/-- **The universal `p`-typical strict coordinate** over `ℤ[v₁, v₂, …][t₁, t₂, …]`, whose inverse
power series is `X +_F ∑^F_{i ≥ 1} tᵢ X^(pⁱ)` for the base change `F` of
`universalHazewinkelIntegralFormalGroup p` along `η_L = C`. -/
def universalStrictCoordinate :
    FormalCoordinate (MvPolynomial ℕ+ (MvPolynomial ℕ+ ℤ)) :=
  ((universalHazewinkelIntegralFormalGroup p).map C).pTypicalStrictCoordinate p X

/-- Explicit unfolding of `universalStrictCoordinate p`. -/
theorem universalStrictCoordinate_def :
    universalStrictCoordinate p =
      ((universalHazewinkelIntegralFormalGroup p).map C).pTypicalStrictCoordinate p X :=
  (rfl)

/-- The linear coefficient of `universalStrictCoordinate p` is `1`. -/
@[simp]
theorem linearCoeff_universalStrictCoordinate :
    FormalCoordinate.linearCoeff (universalStrictCoordinate p) = 1 :=
  FormalGroup.linearCoeff_pTypicalStrictCoordinate _ _ _

/-- `universalStrictCoordinate p` lies in the kernel of `FormalCoordinate.linearCoeff`. -/
theorem universalStrictCoordinate_mem_ker :
    universalStrictCoordinate p ∈
      (FormalCoordinate.linearCoeff (R := MvPolynomial ℕ+ (MvPolynomial ℕ+ ℤ))).ker :=
  FormalGroup.pTypicalStrictCoordinate_mem_ker_linearCoeff _ _ _

/-- Base-changing `universalStrictCoordinate p` along `f` gives `pTypicalStrictCoordinate p (f ∘ X)`
on the source Hazewinkel formal group law classified by `f ∘ C`. -/
theorem map_universalStrictCoordinate (f : MvPolynomial ℕ+ (MvPolynomial ℕ+ ℤ) →+* R) :
    FormalCoordinate.map f (universalStrictCoordinate p) =
      ((universalHazewinkelIntegralFormalGroup p).map (f.comp C)).pTypicalStrictCoordinate
        p (f ∘ X) := by
  rw [universalStrictCoordinate, FormalGroup.map_pTypicalStrictCoordinate, FormalGroup.map_comp]

/-- Base-changing `universalStrictCoordinate p` along `f` is strict. -/
theorem map_universalStrictCoordinate_mem_ker (f : MvPolynomial ℕ+ (MvPolynomial ℕ+ ℤ) →+* R) :
    FormalCoordinate.map f (universalStrictCoordinate p) ∈
      (FormalCoordinate.linearCoeff (R := R)).ker := by
  rw [map_universalStrictCoordinate]
  exact FormalGroup.pTypicalStrictCoordinate_mem_ker_linearCoeff _ _ _

/-- A ring homomorphism out of `ℤ[v₁, v₂, …][t₁, t₂, …]` is determined by its restriction along
`η_L = C` and by its base change of `universalStrictCoordinate p`. -/
theorem ringHom_ext_universalStrictCoordinate {f g : MvPolynomial ℕ+ (MvPolynomial ℕ+ ℤ) →+* R}
    (hC : f.comp C = g.comp C)
    (hφ : FormalCoordinate.map f (universalStrictCoordinate p) =
      FormalCoordinate.map g (universalStrictCoordinate p)) :
    f = g := by
  rw [map_universalStrictCoordinate, map_universalStrictCoordinate, hC] at hφ
  have hX : f ∘ X = g ∘ X :=
    FormalGroup.pTypicalStrictCoordinate_injective _ hp.out.one_lt hφ
  exact ringHom_ext' hC (congrFun hX)

omit p hp in
/-- **Pairs `(v, t)` of sequences in `R` correspond to ring homomorphisms
`ℤ[v₁, v₂, …][t₁, t₂, …] →+* R`**: `v` gives the restriction to `ℤ[v₁, v₂, …]` and `t` gives the
images of the `tᵢ`. -/
def coordinateChangeLift :
    (ℕ+ → R) × (ℕ+ → R) ≃ (MvPolynomial ℕ+ (MvPolynomial ℕ+ ℤ) →+* R) where
  toFun vt := eval₂Hom (MvPolynomial.homEquiv.symm vt.1) vt.2
  invFun f := (f.comp C ∘ X, f ∘ X)
  left_inv vt := Prod.ext (funext fun i ↦ by simp [MvPolynomial.homEquiv])
    (funext fun i ↦ by simp)
  right_inv f := ringHom_ext'
    ((RingHom.ext (eval₂Hom_C _ _)).trans (MvPolynomial.homEquiv.left_inv (f.comp C)))
    fun i ↦ by simp

omit p hp in
@[simp]
theorem coordinateChangeLift_symm_apply_fst (f : MvPolynomial ℕ+ (MvPolynomial ℕ+ ℤ) →+* R) :
    (coordinateChangeLift.symm f).1 = f.comp C ∘ X :=
  (rfl)

omit p hp in
@[simp]
theorem coordinateChangeLift_symm_apply_snd (f : MvPolynomial ℕ+ (MvPolynomial ℕ+ ℤ) →+* R) :
    (coordinateChangeLift.symm f).2 = f ∘ X :=
  (rfl)

omit p hp in
@[simp]
theorem coordinateChangeLift_comp_C (vt : (ℕ+ → R) × (ℕ+ → R)) :
    (coordinateChangeLift vt).comp C = MvPolynomial.homEquiv.symm vt.1 :=
  RingHom.ext (eval₂Hom_C _ _)

omit p hp in
@[simp]
theorem coordinateChangeLift_C (vt : (ℕ+ → R) × (ℕ+ → R)) (a : MvPolynomial ℕ+ ℤ) :
    coordinateChangeLift vt (C a) = MvPolynomial.homEquiv.symm vt.1 a :=
  eval₂Hom_C _ _ a

omit p hp in
theorem coordinateChangeLift_C_X (vt : (ℕ+ → R) × (ℕ+ → R)) (i : ℕ+) :
    coordinateChangeLift vt (C (X i)) = vt.1 i := by
  simp [coordinateChangeLift, MvPolynomial.homEquiv]

omit p hp in
@[simp]
theorem coordinateChangeLift_X (vt : (ℕ+ → R) × (ℕ+ → R)) (i : ℕ+) :
    coordinateChangeLift vt (X i) = vt.2 i :=
  eval₂Hom_X' _ _ i

/-- `coordinateChangeLift (v, t)` specializes `universalStrictCoordinate p` to
`(hazewinkelIntegralFormalGroup p v).pTypicalStrictCoordinate p t`. -/
@[simp]
theorem map_coordinateChangeLift_universalStrictCoordinate (vt : (ℕ+ → R) × (ℕ+ → R)) :
    FormalCoordinate.map (coordinateChangeLift vt) (universalStrictCoordinate p) =
      (hazewinkelIntegralFormalGroup p vt.1).pTypicalStrictCoordinate p vt.2 := by
  rw [map_universalStrictCoordinate, coordinateChangeLift_comp_C,
    map_universalHazewinkelIntegralFormalGroup]
  have hv : ⇑(MvPolynomial.homEquiv.symm vt.1) ∘ X = vt.1 :=
    MvPolynomial.homEquiv.right_inv vt.1
  have ht : ⇑(coordinateChangeLift vt) ∘ X = vt.2 := funext (coordinateChangeLift_X vt)
  rw [hv, ht]

/-! ### The right unit and the counit -/

/-- The **right unit** `η_R : ℤ[v₁, v₂, …] →+* ℤ[v₁, v₂, …][t₁, t₂, …]`, classifying the target
Hazewinkel formal group law obtained by transporting the universal Hazewinkel law along
`universalStrictCoordinate p`. -/
def rightUnit : MvPolynomial ℕ+ ℤ →+* MvPolynomial ℕ+ (MvPolynomial ℕ+ ℤ) :=
  MvPolynomial.homEquiv.symm
    (existsUnique_pTypicalStrictCoordinate_smul_hazewinkelIntegralFormalGroup p
      (C ∘ (X : ℕ+ → MvPolynomial ℕ+ ℤ)) X).choose

/-- Base-changing `universalHazewinkelIntegralFormalGroup p` along `rightUnit p` gives the action of
`universalStrictCoordinate p` on its base change along `η_L = C`. -/
theorem map_rightUnit :
    (universalHazewinkelIntegralFormalGroup p).map (rightUnit p) =
      universalStrictCoordinate p • (universalHazewinkelIntegralFormalGroup p).map C := by
  have hw := (existsUnique_pTypicalStrictCoordinate_smul_hazewinkelIntegralFormalGroup p
    (C ∘ (X : ℕ+ → MvPolynomial ℕ+ ℤ)) X).choose_spec.1
  have hX : ⇑(rightUnit p) ∘ X =
      (existsUnique_pTypicalStrictCoordinate_smul_hazewinkelIntegralFormalGroup p
        (C ∘ (X : ℕ+ → MvPolynomial ℕ+ ℤ)) X).choose :=
    MvPolynomial.homEquiv.right_inv _
  rw [map_universalHazewinkelIntegralFormalGroup, hX, ← hw, universalStrictCoordinate,
    map_universalHazewinkelIntegralFormalGroup]

/-- For any `f : ℤ[v₁, v₂, …][t₁, t₂, …] →+* R`, `f ∘ rightUnit p` classifies the target of the
`p`-typical strict coordinate classified by `f`. -/
theorem map_comp_rightUnit (f : MvPolynomial ℕ+ (MvPolynomial ℕ+ ℤ) →+* R) :
    (universalHazewinkelIntegralFormalGroup p).map (f.comp (rightUnit p)) =
      FormalCoordinate.map f (universalStrictCoordinate p) •
        (universalHazewinkelIntegralFormalGroup p).map (f.comp C) := by
  rw [← FormalGroup.map_comp, map_rightUnit, FormalGroup.map_smul, FormalGroup.map_comp]

omit p hp in
/-- The **counit** `ε : ℤ[v₁, v₂, …][t₁, t₂, …] →+* ℤ[v₁, v₂, …]`, sending `tᵢ ↦ 0` and classifying
the identity coordinate on `universalHazewinkelIntegralFormalGroup p`. -/
def counit : MvPolynomial ℕ+ (MvPolynomial ℕ+ ℤ) →+* MvPolynomial ℕ+ ℤ :=
  eval₂Hom (RingHom.id _) 0

omit p hp in
@[simp]
theorem counit_X (i : ℕ+) : counit (X i) = 0 := by
  simp [counit]

omit p hp in
/-- `ε ∘ η_L = id`: the counit is a retraction of the left unit. -/
@[simp]
theorem counit_comp_C : counit.comp C = RingHom.id (MvPolynomial ℕ+ ℤ) :=
  RingHom.ext (eval₂Hom_C _ _)

omit p hp in
@[simp]
theorem counit_C (a : MvPolynomial ℕ+ ℤ) : counit (C a) = a :=
  eval₂Hom_C _ _ a

/-- The counit sends `universalStrictCoordinate p` to the identity coordinate `1`. -/
@[simp]
theorem map_counit_universalStrictCoordinate :
    FormalCoordinate.map counit (universalStrictCoordinate p) = 1 := by
  rw [map_universalStrictCoordinate, counit_comp_C, FormalGroup.map_id,
    show ⇑counit ∘ X = 0 from funext counit_X, FormalGroup.pTypicalStrictCoordinate_zero]

/-- `ε ∘ η_R = id`: the counit is a retraction of the right unit. -/
@[simp]
theorem counit_comp_rightUnit : counit.comp (rightUnit p) = RingHom.id (MvPolynomial ℕ+ ℤ) :=
  hom_ext p <| by
    rw [map_comp_rightUnit, map_counit_universalStrictCoordinate, counit_comp_C, one_smul]

@[simp]
theorem counit_rightUnit (a : MvPolynomial ℕ+ ℤ) : counit (rightUnit p a) = a :=
  RingHom.congr_fun (counit_comp_rightUnit p) a

/-! ### Full classification of strict isomorphisms over `p`-local and `𝔽_p`-algebras -/

/-- Over a commutative ring `R` in which every prime `q ≠ p` is a unit, **ring homomorphisms
`ℤ[v₁, v₂, …][t₁, t₂, …] →+* R` classify all strict isomorphisms between Hazewinkel formal group
laws over `R`**: triples `(v, w, φ)` of source parameters `v`, target parameters `w`, and a strict
coordinate `φ` with `φ • F_v = F_w`. -/
def strictIsoEquiv (hlocal : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) :
    {q : (ℕ+ → R) × (ℕ+ → R) × (FormalCoordinate.linearCoeff (R := R)).ker //
      q.2.2.1 • hazewinkelIntegralFormalGroup p q.1 = hazewinkelIntegralFormalGroup p q.2.1} ≃
      (MvPolynomial ℕ+ (MvPolynomial ℕ+ ℤ) →+* R) where
  toFun q := coordinateChangeLift (q.1.1,
    (existsUnique_pTypicalStrictCoordinate_eq_of_smul_eq p hlocal
      (MonoidHom.mem_ker.mp q.1.2.2.2) q.2).choose)
  invFun f := ⟨(f.comp C ∘ X, f.comp (rightUnit p) ∘ X,
    ⟨FormalCoordinate.map f (universalStrictCoordinate p),
      map_universalStrictCoordinate_mem_ker p f⟩), by
    have h := (map_comp_rightUnit p f).symm
    rwa [map_universalHazewinkelIntegralFormalGroup,
      map_universalHazewinkelIntegralFormalGroup] at h⟩
  left_inv q := by
    rcases q with ⟨⟨v, w, φ⟩, hsmul⟩
    have hφ1 : FormalCoordinate.linearCoeff φ.1 = 1 := MonoidHom.mem_ker.mp φ.2
    set t := (existsUnique_pTypicalStrictCoordinate_eq_of_smul_eq p hlocal hφ1 hsmul).choose
    have ht : φ.1 = (hazewinkelIntegralFormalGroup p v).pTypicalStrictCoordinate p t :=
      (existsUnique_pTypicalStrictCoordinate_eq_of_smul_eq p hlocal hφ1 hsmul).choose_spec.1
    set f := coordinateChangeLift (v, t)
    have hv : ⇑(f.comp C) ∘ X = v := funext (coordinateChangeLift_C_X (v, t))
    have hφ : FormalCoordinate.map f (universalStrictCoordinate p) = φ.1 := by
      rw [map_coordinateChangeLift_universalStrictCoordinate, ht]
    have hw : ⇑(f.comp (rightUnit p)) ∘ X = w := by
      apply hazewinkelIntegralFormalGroup_injective p
      have h := map_comp_rightUnit p f
      rwa [map_universalHazewinkelIntegralFormalGroup,
        map_universalHazewinkelIntegralFormalGroup, hv, hφ, hsmul] at h
    exact Subtype.ext (Prod.ext hv (Prod.ext hw (Subtype.ext hφ)))
  right_inv f := by
    have h := (map_comp_rightUnit p f).symm
    rw [map_universalHazewinkelIntegralFormalGroup,
      map_universalHazewinkelIntegralFormalGroup] at h
    have hφ1 : FormalCoordinate.linearCoeff
        (FormalCoordinate.map f (universalStrictCoordinate p)) = 1 :=
      MonoidHom.mem_ker.mp (map_universalStrictCoordinate_mem_ker p f)
    have hφ : FormalCoordinate.map f (universalStrictCoordinate p) =
        (hazewinkelIntegralFormalGroup p (f.comp C ∘ X)).pTypicalStrictCoordinate p (f ∘ X) := by
      rw [map_universalStrictCoordinate, map_universalHazewinkelIntegralFormalGroup]
    have ht : (existsUnique_pTypicalStrictCoordinate_eq_of_smul_eq p hlocal hφ1 h).choose =
        f ∘ X :=
      ((existsUnique_pTypicalStrictCoordinate_eq_of_smul_eq p hlocal hφ1 h).choose_spec.2
        (f ∘ X) hφ).symm
    dsimp only
    rw [ht]
    exact coordinateChangeLift.right_inv f

@[simp]
theorem strictIsoEquiv_symm_fst (hlocal : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R))
    (f : MvPolynomial ℕ+ (MvPolynomial ℕ+ ℤ) →+* R) :
    ((strictIsoEquiv p hlocal).symm f).1.1 = f.comp C ∘ X :=
  (rfl)

@[simp]
theorem strictIsoEquiv_symm_snd_fst (hlocal : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R))
    (f : MvPolynomial ℕ+ (MvPolynomial ℕ+ ℤ) →+* R) :
    ((strictIsoEquiv p hlocal).symm f).1.2.1 = f.comp (rightUnit p) ∘ X :=
  (rfl)

@[simp]
theorem strictIsoEquiv_symm_snd_snd (hlocal : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R))
    (f : MvPolynomial ℕ+ (MvPolynomial ℕ+ ℤ) →+* R) :
    ((strictIsoEquiv p hlocal).symm f).1.2.2.1 =
      FormalCoordinate.map f (universalStrictCoordinate p) :=
  (rfl)

/-- **Representability of `BP_*BP` over `ℤ_(p)`**: for any localization `A` of `ℤ` at `(p)` and any
`A`-algebra `R`, `A`-algebra homomorphisms out of `BP_*BP = A[v₁, v₂, …][t₁, t₂, …]` classify all
strict isomorphisms between Hazewinkel formal group laws over `R`. -/
def strictIsoAlgEquiv (A : Type*) [CommRing A]
    [IsLocalization.AtPrime A (Ideal.span {(p : ℤ)})] [Algebra A R] :
    {q : (ℕ+ → R) × (ℕ+ → R) × (FormalCoordinate.linearCoeff (R := R)).ker //
      q.2.2.1 • hazewinkelIntegralFormalGroup p q.1 = hazewinkelIntegralFormalGroup p q.2.1} ≃
      (MvPolynomial ℕ+ (MvPolynomial ℕ+ A) →ₐ[A] R) :=
  have hlocal : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R) := fun q hq hqp ↦ by
    have hA : IsUnit (algebraMap ℤ A q) :=
      (IsLocalization.AtPrime.isUnit_to_map_iff A (Ideal.span {(p : ℤ)}) (q : ℤ)).mpr <|
        Ideal.mem_primeCompl_iff.mpr fun hmem ↦ hqp
          ((Nat.prime_dvd_prime_iff_eq hp.out hq).mp
            (Int.natCast_dvd_natCast.mp (Ideal.mem_span_singleton.mp hmem))).symm
    have hqA : IsUnit (q : A) := by simpa only [map_natCast] using hA
    simpa only [map_natCast] using hqA.map (algebraMap A R)
  (strictIsoEquiv p hlocal).trans
    { toFun f :=
        { toRingHom := eval₂Hom (MvPolynomial.aeval (f.comp C ∘ X)).toRingHom (f ∘ X)
          commutes' a := by
            rw [IsScalarTower.algebraMap_apply A (MvPolynomial ℕ+ A), MvPolynomial.algebraMap_eq,
              MvPolynomial.algebraMap_eq]
            simp }
      invFun g := g.toRingHom.comp (map (map (Int.castRingHom A)))
      left_inv f := by
        refine ringHom_ext' ?_ fun i ↦ by simp
        apply MvPolynomial.homEquiv.injective
        funext i
        simp [MvPolynomial.homEquiv]
      right_inv g := by
        apply AlgHom.toRingHom_injective
        refine ringHom_ext' ?_ fun i ↦ by simp
        let lhs : MvPolynomial ℕ+ A →ₐ[A] R :=
          { toRingHom := (eval₂Hom (MvPolynomial.aeval
                ((g.toRingHom.comp (map (map (Int.castRingHom A)))).comp C ∘ X)).toRingHom
              (g.toRingHom.comp (map (map (Int.castRingHom A))) ∘ X)).comp C
            commutes' a := by simp }
        let rhs : MvPolynomial ℕ+ A →ₐ[A] R :=
          { toRingHom := g.toRingHom.comp C
            commutes' a := by simpa using g.commutes a }
        exact congrArg AlgHom.toRingHom
          (MvPolynomial.algHom_ext (f := lhs) (g := rhs) fun i ↦ by simp [lhs, rhs]) }

@[simp]
theorem strictIsoAlgEquiv_symm_fst (A : Type*) [CommRing A]
    [IsLocalization.AtPrime A (Ideal.span {(p : ℤ)})] [Algebra A R]
    (g : MvPolynomial ℕ+ (MvPolynomial ℕ+ A) →ₐ[A] R) (i : ℕ+) :
    ((strictIsoAlgEquiv p A).symm g).1.1 i = g (C (X i)) := by
  simp [strictIsoAlgEquiv]

@[simp]
theorem strictIsoAlgEquiv_symm_snd_snd (A : Type*) [CommRing A]
    [IsLocalization.AtPrime A (Ideal.span {(p : ℤ)})] [Algebra A R]
    (g : MvPolynomial ℕ+ (MvPolynomial ℕ+ A) →ₐ[A] R) :
    ((strictIsoAlgEquiv p A).symm g).1.2.2.1 =
      FormalCoordinate.map (g.toRingHom.comp (map (map (Int.castRingHom A))))
        (universalStrictCoordinate p) :=
  (rfl)

/-- Over any commutative ring `R` of characteristic `p`, ring homomorphisms
`ℤ[v₁, v₂, …][t₁, t₂, …] →+* R` classify all strict isomorphisms between Hazewinkel formal group
laws over `R`. -/
def strictIsoEquivOfCharP [CharP R p] :
    {q : (ℕ+ → R) × (ℕ+ → R) × (FormalCoordinate.linearCoeff (R := R)).ker //
      q.2.2.1 • hazewinkelIntegralFormalGroup p q.1 = hazewinkelIntegralFormalGroup p q.2.1} ≃
      (MvPolynomial ℕ+ (MvPolynomial ℕ+ ℤ) →+* R) :=
  strictIsoEquiv p fun q hq hqp ↦ by
    have hcop : Nat.Coprime q p := hq.coprime_iff_not_dvd.mpr fun hdvd ↦
      hqp ((Nat.prime_dvd_prime_iff_eq hq hp.out).mp hdvd)
    have hbez := congrArg (Int.castRingHom R) (Nat.gcd_eq_gcd_ab q p)
    rw [hcop.gcd_eq_one, Nat.cast_one, map_one, map_add, map_mul, map_mul, map_natCast,
      map_natCast, CharP.cast_eq_zero R p, zero_mul, add_zero] at hbez
    exact IsUnit.of_mul_eq_one (Nat.gcdA q p : R) hbez.symm

@[simp]
theorem strictIsoEquivOfCharP_symm_fst [CharP R p]
    (f : MvPolynomial ℕ+ (MvPolynomial ℕ+ ℤ) →+* R) :
    ((strictIsoEquivOfCharP p).symm f).1.1 = f.comp C ∘ X :=
  (rfl)

@[simp]
theorem strictIsoEquivOfCharP_symm_snd_fst [CharP R p]
    (f : MvPolynomial ℕ+ (MvPolynomial ℕ+ ℤ) →+* R) :
    ((strictIsoEquivOfCharP p).symm f).1.2.1 = f.comp (rightUnit p) ∘ X :=
  (rfl)

@[simp]
theorem strictIsoEquivOfCharP_symm_snd_snd [CharP R p]
    (f : MvPolynomial ℕ+ (MvPolynomial ℕ+ ℤ) →+* R) :
    ((strictIsoEquivOfCharP p).symm f).1.2.2.1 =
      FormalCoordinate.map f (universalStrictCoordinate p) :=
  (rfl)

/-! ### The tensor square `Γ_p ⊗_V Γ_p` -/

/-- **The universal property of `Γ_p ⊗_V Γ_p`**, for `V = ℤ[v₁, v₂, …]` and `Γ_p = V[t₁, t₂, …]`:
ring homomorphisms out of `MvPolynomial ℕ+ Γ_p` correspond to pairs `(f, g)` of ring homomorphisms
out of `Γ_p` with `f ∘ η_R = g ∘ η_L`, by restriction along the left factor `C` and the right
factor `MvPolynomial.map (rightUnit p)`. -/
def tensorLift :
    {fg : (MvPolynomial ℕ+ (MvPolynomial ℕ+ ℤ) →+* R) ×
        (MvPolynomial ℕ+ (MvPolynomial ℕ+ ℤ) →+* R) //
      fg.1.comp (rightUnit p) = fg.2.comp C} ≃
      (MvPolynomial ℕ+ (MvPolynomial ℕ+ (MvPolynomial ℕ+ ℤ)) →+* R) where
  toFun fg := eval₂Hom fg.1.1 (fg.1.2 ∘ X)
  invFun k := ⟨(k.comp C, k.comp (map (rightUnit p))), by
    rw [RingHom.comp_assoc, RingHom.comp_assoc, map_comp_C]⟩
  left_inv fg := by
    have hC : (eval₂Hom fg.1.1 (fg.1.2 ∘ X)).comp C = fg.1.1 :=
      RingHom.ext (eval₂Hom_C _ _)
    refine Subtype.ext (Prod.ext hC ?_)
    refine ringHom_ext' ?_ fun i ↦ by simp
    rw [RingHom.comp_assoc, map_comp_C, ← RingHom.comp_assoc, hC, fg.2]
  right_inv k := ringHom_ext' (RingHom.ext fun a ↦ by simp) fun i ↦ by simp

@[simp]
theorem tensorLift_symm_apply_fst
    (k : MvPolynomial ℕ+ (MvPolynomial ℕ+ (MvPolynomial ℕ+ ℤ)) →+* R) :
    ((tensorLift p).symm k).1.1 = k.comp C :=
  (rfl)

@[simp]
theorem tensorLift_symm_apply_snd
    (k : MvPolynomial ℕ+ (MvPolynomial ℕ+ (MvPolynomial ℕ+ ℤ)) →+* R) :
    ((tensorLift p).symm k).1.2 = k.comp (map (rightUnit p)) :=
  (rfl)

@[simp]
theorem tensorLift_comp_C
    (fg : {fg : (MvPolynomial ℕ+ (MvPolynomial ℕ+ ℤ) →+* R) ×
        (MvPolynomial ℕ+ (MvPolynomial ℕ+ ℤ) →+* R) //
      fg.1.comp (rightUnit p) = fg.2.comp C}) :
    (tensorLift p fg).comp C = fg.1.1 :=
  congrArg (fun q ↦ q.1.1) ((tensorLift p).left_inv fg)

@[simp]
theorem tensorLift_comp_map_rightUnit
    (fg : {fg : (MvPolynomial ℕ+ (MvPolynomial ℕ+ ℤ) →+* R) ×
        (MvPolynomial ℕ+ (MvPolynomial ℕ+ ℤ) →+* R) //
      fg.1.comp (rightUnit p) = fg.2.comp C}) :
    (tensorLift p fg).comp (map (rightUnit p)) = fg.1.2 :=
  congrArg (fun q ↦ q.1.2) ((tensorLift p).left_inv fg)

@[simp]
theorem tensorLift_C
    (fg : {fg : (MvPolynomial ℕ+ (MvPolynomial ℕ+ ℤ) →+* R) ×
        (MvPolynomial ℕ+ (MvPolynomial ℕ+ ℤ) →+* R) //
      fg.1.comp (rightUnit p) = fg.2.comp C})
    (x : MvPolynomial ℕ+ (MvPolynomial ℕ+ ℤ)) :
    tensorLift p fg (C x) = fg.1.1 x :=
  RingHom.congr_fun (tensorLift_comp_C p fg) x

@[simp]
theorem tensorLift_map_rightUnit
    (fg : {fg : (MvPolynomial ℕ+ (MvPolynomial ℕ+ ℤ) →+* R) ×
        (MvPolynomial ℕ+ (MvPolynomial ℕ+ ℤ) →+* R) //
      fg.1.comp (rightUnit p) = fg.2.comp C})
    (x : MvPolynomial ℕ+ (MvPolynomial ℕ+ ℤ)) :
    tensorLift p fg (map (rightUnit p) x) = fg.1.2 x :=
  RingHom.congr_fun (tensorLift_comp_map_rightUnit p fg) x

@[simp]
theorem tensorLift_X
    (fg : {fg : (MvPolynomial ℕ+ (MvPolynomial ℕ+ ℤ) →+* R) ×
        (MvPolynomial ℕ+ (MvPolynomial ℕ+ ℤ) →+* R) //
      fg.1.comp (rightUnit p) = fg.2.comp C}) (i : ℕ+) :
    tensorLift p fg (X i) = fg.1.2 (X i) := by
  simpa using tensorLift_map_rightUnit p fg (X i)

/-- A ring homomorphism out of `Γ_p ⊗_V Γ_p` is determined by its restrictions to both factors. -/
theorem tensor_ringHom_ext
    {k k' : MvPolynomial ℕ+ (MvPolynomial ℕ+ (MvPolynomial ℕ+ ℤ)) →+* R}
    (h₁ : k.comp C = k'.comp C)
    (h₂ : k.comp (map (rightUnit p)) = k'.comp (map (rightUnit p))) :
    k = k' :=
  (tensorLift p).symm.injective (Subtype.ext (Prod.ext h₁ h₂))

/-! ### Integral descent of `p`-typical strict coordinates -/

private theorem pTypicalParams_mem_range_of_injective
    {A B : Type*} [CommRing A] [CommRing B] {ι : A →+* B} (v : ℕ+ → A) (φ : FormalCoordinate A)
    {tB : ℕ+ → B}
    (hcurveB : (FormalCoordinate.map ι φ)⁻¹.toPowerSeries =
      ((hazewinkelIntegralFormalGroup p (ι ∘ v)).pTypicalStrictCurve p tB).toPowerSeries) :
    ∀ n (i : ℕ+), (i : ℕ) ≤ n → tB i ∈ ι.range := by
  intro n
  induction n with
  | zero => intro i hi; have := i.pos; omega
  | succ n ih =>
    intro i hi
    rcases lt_or_eq_of_le hi with hlt | heq
    · exact ih i (Nat.lt_succ_iff.mp hlt)
    · obtain rfl : i = n.succPNat := PNat.coe_injective heq
      let t_trunc : ℕ+ → A := fun j ↦ if hj : (j : ℕ) ≤ n then (ih j hj).choose else 0
      have htrunc : ∀ j : ℕ+, (j : ℕ) ≤ n → tB j = (ι ∘ t_trunc) j := fun j hj ↦ by
        dsimp only [t_trunc, Function.comp_apply]
        rw [dite_eq_left hj]
        exact (ih j hj).choose_spec.symm
      have hsub := (hazewinkelIntegralFormalGroup p (ι ∘ v)).coeff_pow_succ_pTypicalStrictCurve_sub
        hp.out.one_lt htrunc
      have ht0 : (ι ∘ t_trunc) n.succPNat = 0 := by simp [t_trunc]
      rw [ht0, sub_zero, ← hcurveB, ← map_inv, FormalCoordinate.toPowerSeries_map,
        ← map_hazewinkelIntegralFormalGroup, ← FormalGroup.map_pTypicalStrictCurve,
        FormalGroup.Curve.toPowerSeries_map, ← map_sub (PowerSeries.map ι),
        PowerSeries.coeff_map] at hsub
      exact ⟨_, hsub⟩

/-- **Integral descent of `p`-typical strict coordinates**: if `A` embeds into a `ℚ`-algebra `B`
via an injective ring homomorphism `ι : A →+* B`, then any strict coordinate `φ` over `A`
transporting `hazewinkelIntegralFormalGroup p v` to `hazewinkelIntegralFormalGroup p w` is
`pTypicalStrictCoordinate p t` for a unique `t : ℕ+ → A`. -/
theorem existsUnique_pTypicalStrictCoordinate_eq_of_smul_eq_of_injective
    {A B : Type*} [CommRing A] [CommRing B] [Algebra ℚ B] {ι : A →+* B}
    (hι : Function.Injective ι) {v w : ℕ+ → A} {φ : FormalCoordinate A}
    (hφ : FormalCoordinate.linearCoeff φ = 1)
    (hsmul : φ • hazewinkelIntegralFormalGroup p v = hazewinkelIntegralFormalGroup p w) :
    ∃! t : ℕ+ → A, φ = (hazewinkelIntegralFormalGroup p v).pTypicalStrictCoordinate p t := by
  have hlocalB : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : B) := fun q hq _ ↦ by
    have hqQ : IsUnit (q : ℚ) := isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr hq.ne_zero)
    simpa only [map_natCast] using hqQ.map (algebraMap ℚ B)
  have hφB : FormalCoordinate.linearCoeff (FormalCoordinate.map ι φ) = 1 := by
    ext
    have hφ1 : PowerSeries.coeff 1 φ.toPowerSeries = 1 := by
      rw [← FormalCoordinate.val_linearCoeff, hφ, Units.val_one]
    simp [FormalCoordinate.val_linearCoeff, hφ1]
  have hsmulB : FormalCoordinate.map ι φ • hazewinkelIntegralFormalGroup p (ι ∘ v) =
      hazewinkelIntegralFormalGroup p (ι ∘ w) := by
    have h := congrArg (fun F : FormalGroup A ↦ F.map ι) hsmul
    simpa only [FormalGroup.map_smul, map_hazewinkelIntegralFormalGroup] using h
  obtain ⟨tB, htB, _⟩ :=
    existsUnique_pTypicalStrictCoordinate_eq_of_smul_eq p hlocalB hφB hsmulB
  have hcurveB : (FormalCoordinate.map ι φ)⁻¹.toPowerSeries =
      ((hazewinkelIntegralFormalGroup p (ι ∘ v)).pTypicalStrictCurve p tB).toPowerSeries := by
    rw [htB, FormalGroup.toPowerSeries_inv_pTypicalStrictCoordinate]
  have hmem := pTypicalParams_mem_range_of_injective p v φ hcurveB
  let tA : ℕ+ → A := fun i ↦ (hmem i.val i le_rfl).choose
  have htA : φ = (hazewinkelIntegralFormalGroup p v).pTypicalStrictCoordinate p tA := by
    have hmap : FormalCoordinate.map ι φ =
        FormalCoordinate.map ι
          ((hazewinkelIntegralFormalGroup p v).pTypicalStrictCoordinate p tA) := by
      rw [htB, FormalGroup.map_pTypicalStrictCoordinate, map_hazewinkelIntegralFormalGroup]
      congr 1
      exact funext fun i ↦ (hmem i.val i le_rfl).choose_spec.symm
    ext1
    apply PowerSeries.ext fun k ↦ hι ?_
    simpa only [FormalCoordinate.toPowerSeries_map, PowerSeries.coeff_map] using
      congrArg (fun ψ : FormalCoordinate B ↦ PowerSeries.coeff k ψ.toPowerSeries) hmap
  exact ⟨tA, htA, fun t' ht' ↦
    (hazewinkelIntegralFormalGroup p v).pTypicalStrictCoordinate_injective hp.out.one_lt
      (ht'.symm.trans htA)⟩

/-! ### The coproduct -/

private theorem existsUnique_coproduct_params :
    ∃! t : ℕ+ → MvPolynomial ℕ+ (MvPolynomial ℕ+ (MvPolynomial ℕ+ ℤ)),
      FormalCoordinate.map (map (rightUnit p)) (universalStrictCoordinate p) *
          FormalCoordinate.map C (universalStrictCoordinate p) =
        (hazewinkelIntegralFormalGroup p
          (⇑(C.comp (C : MvPolynomial ℕ+ ℤ →+* MvPolynomial ℕ+ (MvPolynomial ℕ+ ℤ))) ∘
            X)).pTypicalStrictCoordinate p t := by
  let ι : MvPolynomial ℕ+ (MvPolynomial ℕ+ (MvPolynomial ℕ+ ℤ)) →+*
      MvPolynomial ℕ+ (MvPolynomial ℕ+ (MvPolynomial ℕ+ ℚ)) :=
    map (map (map (Int.castRingHom ℚ)))
  have hι : Function.Injective ι :=
    map_injective _ (map_injective _ (map_injective _ Int.cast_injective))
  refine existsUnique_pTypicalStrictCoordinate_eq_of_smul_eq_of_injective p
    (B := MvPolynomial ℕ+ (MvPolynomial ℕ+ (MvPolynomial ℕ+ ℚ))) (ι := ι) hι
    (w := ⇑((map (rightUnit p)).comp (rightUnit p)) ∘ X)
    (MonoidHom.mem_ker.mp (mul_mem (map_universalStrictCoordinate_mem_ker p _)
      (map_universalStrictCoordinate_mem_ker p _))) ?_
  rw [← map_universalHazewinkelIntegralFormalGroup, ← map_universalHazewinkelIntegralFormalGroup,
    mul_smul,
    ← map_comp_rightUnit (R := MvPolynomial ℕ+ (MvPolynomial ℕ+ (MvPolynomial ℕ+ ℤ))) p C,
    ← map_comp_C (rightUnit p),
    ← map_comp_rightUnit (R := MvPolynomial ℕ+ (MvPolynomial ℕ+ (MvPolynomial ℕ+ ℤ))) p
      (map (rightUnit p))]

/-- The **coproduct** `Δ : Γ_p →+* Γ_p ⊗_V Γ_p`, classifying the composite `ψ * φ = ψ ∘ φ` of the
universal composable pair of `p`-typical strict coordinate changes. -/
def coproduct :
    MvPolynomial ℕ+ (MvPolynomial ℕ+ ℤ) →+*
      MvPolynomial ℕ+ (MvPolynomial ℕ+ (MvPolynomial ℕ+ ℤ)) :=
  coordinateChangeLift
    (⇑(C.comp (C : MvPolynomial ℕ+ ℤ →+* MvPolynomial ℕ+ (MvPolynomial ℕ+ ℤ))) ∘ X,
      (existsUnique_coproduct_params p).choose)

/-- `Δ ∘ η_L = (η_L ⊗ 1) ∘ η_L`: the source of a composite is the source of its first factor. -/
@[simp]
theorem coproduct_comp_C : (coproduct p).comp C = C.comp C := by
  rw [coproduct, coordinateChangeLift_comp_C]
  exact MvPolynomial.homEquiv.symm_apply_eq.mpr rfl

@[simp]
theorem coproduct_C (a : MvPolynomial ℕ+ ℤ) : coproduct p (C a) = C (C a) :=
  RingHom.congr_fun (coproduct_comp_C p) a

/-- The coproduct sends `universalStrictCoordinate p` to the composite `ψ * φ` of the universal
`p`-typical strict coordinates of the two factors. -/
@[simp]
theorem map_coproduct_universalStrictCoordinate :
    FormalCoordinate.map (coproduct p) (universalStrictCoordinate p) =
      FormalCoordinate.map (map (rightUnit p)) (universalStrictCoordinate p) *
        FormalCoordinate.map C (universalStrictCoordinate p) := by
  rw [coproduct, map_coordinateChangeLift_universalStrictCoordinate,
    ← (existsUnique_coproduct_params p).choose_spec.1]

/-- **The coproduct classifies composition**: if `k : Γ_p ⊗_V Γ_p →+* R` classifies a composable
pair of `p`-typical strict coordinate changes, then `k ∘ Δ` classifies their composite. -/
theorem map_comp_coproduct_universalStrictCoordinate
    (k : MvPolynomial ℕ+ (MvPolynomial ℕ+ (MvPolynomial ℕ+ ℤ)) →+* R) :
    FormalCoordinate.map (k.comp (coproduct p)) (universalStrictCoordinate p) =
      FormalCoordinate.map (k.comp (map (rightUnit p))) (universalStrictCoordinate p) *
        FormalCoordinate.map (k.comp C) (universalStrictCoordinate p) := by
  rw [FormalCoordinate.map_comp
        (R := MvPolynomial ℕ+ (MvPolynomial ℕ+ ℤ))
        (S := MvPolynomial ℕ+ (MvPolynomial ℕ+ (MvPolynomial ℕ+ ℤ))) (T := R),
    map_coproduct_universalStrictCoordinate, map_mul,
    ← FormalCoordinate.map_comp
        (R := MvPolynomial ℕ+ (MvPolynomial ℕ+ ℤ))
        (S := MvPolynomial ℕ+ (MvPolynomial ℕ+ (MvPolynomial ℕ+ ℤ))) (T := R),
    ← FormalCoordinate.map_comp
        (R := MvPolynomial ℕ+ (MvPolynomial ℕ+ ℤ))
        (S := MvPolynomial ℕ+ (MvPolynomial ℕ+ (MvPolynomial ℕ+ ℤ))) (T := R)]

/-- The source classified by `k ∘ Δ` is the source classified by the left factor of `k`. -/
theorem comp_coproduct_comp_C
    (k : MvPolynomial ℕ+ (MvPolynomial ℕ+ (MvPolynomial ℕ+ ℤ)) →+* R) :
    (k.comp (coproduct p)).comp C = (k.comp C).comp C := by
  rw [RingHom.comp_assoc, coproduct_comp_C, RingHom.comp_assoc]

/-- `Δ ∘ η_R = (1 ⊗ η_R) ∘ η_R`: the target of a composite is the target of its second factor. -/
@[simp]
theorem coproduct_comp_rightUnit :
    (coproduct p).comp (rightUnit p) = (map (rightUnit p)).comp (rightUnit p) :=
  hom_ext (R := MvPolynomial ℕ+ (MvPolynomial ℕ+ (MvPolynomial ℕ+ ℤ))) p <| by
    rw [map_comp_rightUnit (R := MvPolynomial ℕ+ (MvPolynomial ℕ+ (MvPolynomial ℕ+ ℤ))) p
        (coproduct p),
      map_coproduct_universalStrictCoordinate, coproduct_comp_C,
      map_comp_rightUnit (R := MvPolynomial ℕ+ (MvPolynomial ℕ+ (MvPolynomial ℕ+ ℤ))) p
        (map (rightUnit p)),
      map_comp_C (rightUnit p),
      map_comp_rightUnit (R := MvPolynomial ℕ+ (MvPolynomial ℕ+ (MvPolynomial ℕ+ ℤ))) p C,
      mul_smul]

@[simp]
theorem coproduct_rightUnit (a : MvPolynomial ℕ+ ℤ) :
    coproduct p (rightUnit p a) = map (rightUnit p) (rightUnit p a) :=
  RingHom.congr_fun (coproduct_comp_rightUnit p) a

/-- **The left counit law** `(ε ⊗ id) ∘ Δ = id`. -/
theorem tensorLift_counit_id_comp_coproduct :
    (tensorLift p ⟨(C.comp counit, RingHom.id _), by
        rw [RingHom.comp_assoc, counit_comp_rightUnit, RingHom.comp_id, RingHom.id_comp]⟩).comp
          (coproduct p) =
      RingHom.id (MvPolynomial ℕ+ (MvPolynomial ℕ+ ℤ)) := by
  refine ringHom_ext_universalStrictCoordinate p ?_ ?_
  · rw [comp_coproduct_comp_C, tensorLift_comp_C, RingHom.comp_assoc, counit_comp_C,
      RingHom.comp_id, RingHom.id_comp]
  · rw [map_comp_coproduct_universalStrictCoordinate, tensorLift_comp_map_rightUnit,
      tensorLift_comp_C]
    simp [FormalCoordinate.map_comp]

/-- **The right counit law** `(id ⊗ ε) ∘ Δ = id`. -/
theorem tensorLift_id_counit_comp_coproduct :
    (tensorLift p ⟨(RingHom.id _, (rightUnit p).comp counit), by
        rw [RingHom.comp_assoc, counit_comp_C, RingHom.comp_id, RingHom.id_comp]⟩).comp
          (coproduct p) =
      RingHom.id (MvPolynomial ℕ+ (MvPolynomial ℕ+ ℤ)) := by
  refine ringHom_ext_universalStrictCoordinate p ?_ ?_
  · rw [comp_coproduct_comp_C, tensorLift_comp_C]
  · rw [map_comp_coproduct_universalStrictCoordinate, tensorLift_comp_map_rightUnit,
      tensorLift_comp_C]
    simp [FormalCoordinate.map_comp]

/-- **Coassociativity for composable triples**: for any composable triple `(f₁, f₂, f₃)` of ring
homomorphisms `Γ_p →+* R`, `(μ₁₂₃ ∘ (Δ ⊗ id)) ∘ Δ = (μ₁₂₃ ∘ (id ⊗ Δ)) ∘ Δ`. -/
theorem tensorLift_coproduct_assoc
    {f₁ f₂ f₃ : MvPolynomial ℕ+ (MvPolynomial ℕ+ ℤ) →+* R}
    (h₁₂ : f₁.comp (rightUnit p) = f₂.comp C)
    (h₂₃ : f₂.comp (rightUnit p) = f₃.comp C) :
    (tensorLift p ⟨((tensorLift p ⟨(f₁, f₂), h₁₂⟩).comp (coproduct p), f₃), by
        rw [RingHom.comp_assoc, coproduct_comp_rightUnit, ← RingHom.comp_assoc,
          tensorLift_comp_map_rightUnit, h₂₃]⟩).comp (coproduct p) =
      (tensorLift p ⟨(f₁, (tensorLift p ⟨(f₂, f₃), h₂₃⟩).comp (coproduct p)), by
        rw [RingHom.comp_assoc, coproduct_comp_C, ← RingHom.comp_assoc,
          tensorLift_comp_C, h₁₂]⟩).comp (coproduct p) := by
  refine ringHom_ext_universalStrictCoordinate p ?_ ?_
  · rw [comp_coproduct_comp_C, comp_coproduct_comp_C, tensorLift_comp_C, tensorLift_comp_C,
      comp_coproduct_comp_C, tensorLift_comp_C]
  · rw [map_comp_coproduct_universalStrictCoordinate,
      map_comp_coproduct_universalStrictCoordinate,
      tensorLift_comp_map_rightUnit, tensorLift_comp_C,
      tensorLift_comp_map_rightUnit, tensorLift_comp_C,
      map_comp_coproduct_universalStrictCoordinate,
      map_comp_coproduct_universalStrictCoordinate,
      tensorLift_comp_map_rightUnit, tensorLift_comp_C,
      tensorLift_comp_map_rightUnit, tensorLift_comp_C, mul_assoc]

/-- **Universal coassociativity** `(Δ ⊗ id) ∘ Δ = (id ⊗ Δ) ∘ Δ` in the triple tensor product
`Γ_p ⊗_V Γ_p ⊗_V Γ_p = MvPolynomial (ℕ+ ⊕ ℕ+) Γ_p`, whose three factors are `C`,
`eval₂Hom (C ∘ η_R) (X ∘ Sum.inl)`, and `eval₂Hom (ι₂ ∘ η_R) (X ∘ Sum.inr)`. -/
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
      ⟨((tensorLift (R := MvPolynomial (ℕ+ ⊕ ℕ+) (MvPolynomial ℕ+ (MvPolynomial ℕ+ ℤ))) p
          ⟨(ι₁, ι₂), h₁₂⟩).comp (coproduct p), ι₃), by
        rw [RingHom.comp_assoc, coproduct_comp_rightUnit, ← RingHom.comp_assoc,
          tensorLift_comp_map_rightUnit, h₂₃]⟩).comp (coproduct p) =
      (tensorLift (R := MvPolynomial (ℕ+ ⊕ ℕ+) (MvPolynomial ℕ+ (MvPolynomial ℕ+ ℤ))) p
        ⟨(ι₁, (tensorLift (R := MvPolynomial (ℕ+ ⊕ ℕ+) (MvPolynomial ℕ+ (MvPolynomial ℕ+ ℤ))) p
          ⟨(ι₂, ι₃), h₂₃⟩).comp (coproduct p)), by
        rw [RingHom.comp_assoc, coproduct_comp_C, ← RingHom.comp_assoc, tensorLift_comp_C,
          h₁₂]⟩).comp (coproduct p) :=
  tensorLift_coproduct_assoc
    (R := MvPolynomial (ℕ+ ⊕ ℕ+) (MvPolynomial ℕ+ (MvPolynomial ℕ+ ℤ))) p
    (RingHom.ext (eval₂Hom_C _ _)).symm (RingHom.ext (eval₂Hom_C _ _)).symm

/-! ### The conjugation -/

private theorem existsUnique_conjugation_params :
    ∃! t : ℕ+ → MvPolynomial ℕ+ (MvPolynomial ℕ+ ℤ),
      (universalStrictCoordinate p)⁻¹ =
        (hazewinkelIntegralFormalGroup p (⇑(rightUnit p) ∘ X)).pTypicalStrictCoordinate p t := by
  let ι : MvPolynomial ℕ+ (MvPolynomial ℕ+ ℤ) →+* MvPolynomial ℕ+ (MvPolynomial ℕ+ ℚ) :=
    map (map (Int.castRingHom ℚ))
  have hι : Function.Injective ι := map_injective _ (map_injective _ Int.cast_injective)
  refine existsUnique_pTypicalStrictCoordinate_eq_of_smul_eq_of_injective p (ι := ι) hι
    (w := C ∘ X) (MonoidHom.mem_ker.mp (inv_mem (universalStrictCoordinate_mem_ker p))) ?_
  rw [← map_universalHazewinkelIntegralFormalGroup, ← map_universalHazewinkelIntegralFormalGroup,
    map_rightUnit, inv_smul_smul]

/-- The **conjugation** `c : Γ_p →+* Γ_p`, classifying the inverse `φ⁻¹ : φ • F_v → F_v` of the
universal `p`-typical strict coordinate change. -/
def conjugation :
    MvPolynomial ℕ+ (MvPolynomial ℕ+ ℤ) →+* MvPolynomial ℕ+ (MvPolynomial ℕ+ ℤ) :=
  coordinateChangeLift (⇑(rightUnit p) ∘ X, (existsUnique_conjugation_params p).choose)

/-- `c ∘ η_L = η_R`: the source of the inverse is the target. -/
@[simp]
theorem conjugation_comp_C : (conjugation p).comp C = rightUnit p := by
  rw [conjugation, coordinateChangeLift_comp_C]
  exact MvPolynomial.homEquiv.symm_apply_eq.mpr rfl

@[simp]
theorem conjugation_C (a : MvPolynomial ℕ+ ℤ) : conjugation p (C a) = rightUnit p a :=
  RingHom.congr_fun (conjugation_comp_C p) a

/-- The conjugation sends `universalStrictCoordinate p` to its inverse. -/
@[simp]
theorem map_conjugation_universalStrictCoordinate :
    FormalCoordinate.map (conjugation p) (universalStrictCoordinate p) =
      (universalStrictCoordinate p)⁻¹ := by
  rw [conjugation, map_coordinateChangeLift_universalStrictCoordinate,
    ← (existsUnique_conjugation_params p).choose_spec.1]

/-- `c ∘ η_R = η_L`: the target of the inverse is the source. -/
@[simp]
theorem conjugation_comp_rightUnit : (conjugation p).comp (rightUnit p) = C :=
  hom_ext p <| by
    rw [map_comp_rightUnit, map_conjugation_universalStrictCoordinate, conjugation_comp_C,
      map_rightUnit, inv_smul_smul]

@[simp]
theorem conjugation_rightUnit (a : MvPolynomial ℕ+ ℤ) :
    conjugation p (rightUnit p a) = C a :=
  RingHom.congr_fun (conjugation_comp_rightUnit p) a

/-- `c ∘ c = id`: conjugation is an involution. -/
@[simp]
theorem conjugation_comp_conjugation :
    (conjugation p).comp (conjugation p) =
      RingHom.id (MvPolynomial ℕ+ (MvPolynomial ℕ+ ℤ)) := by
  refine ringHom_ext_universalStrictCoordinate p ?_ ?_
  · rw [RingHom.comp_assoc, conjugation_comp_C, conjugation_comp_rightUnit, RingHom.id_comp]
  · rw [FormalCoordinate.map_comp, map_conjugation_universalStrictCoordinate, map_inv,
      map_conjugation_universalStrictCoordinate, inv_inv]
    simp

@[simp]
theorem conjugation_conjugation (x : MvPolynomial ℕ+ (MvPolynomial ℕ+ ℤ)) :
    conjugation p (conjugation p x) = x :=
  RingHom.congr_fun (conjugation_comp_conjugation p) x

/-- `ε ∘ c = ε`: the counit is invariant under conjugation. -/
@[simp]
theorem counit_comp_conjugation : counit.comp (conjugation p) = counit := by
  refine ringHom_ext_universalStrictCoordinate p ?_ ?_
  · rw [RingHom.comp_assoc, conjugation_comp_C, counit_comp_rightUnit, counit_comp_C]
  · rw [FormalCoordinate.map_comp, map_conjugation_universalStrictCoordinate, map_inv,
      map_counit_universalStrictCoordinate, inv_one]

@[simp]
theorem counit_conjugation (x : MvPolynomial ℕ+ (MvPolynomial ℕ+ ℤ)) :
    counit (conjugation p x) = counit x :=
  RingHom.congr_fun (counit_comp_conjugation p) x

/-- **The left antipode equation** `μ ∘ (c ⊗ id) ∘ Δ = η_R ∘ ε`. -/
theorem tensorLift_conjugation_id_comp_coproduct :
    (tensorLift p ⟨(conjugation p, RingHom.id _), by
        rw [conjugation_comp_rightUnit, RingHom.id_comp]⟩).comp (coproduct p) =
      (rightUnit p).comp counit := by
  refine ringHom_ext_universalStrictCoordinate p ?_ ?_
  · rw [comp_coproduct_comp_C, tensorLift_comp_C, conjugation_comp_C, RingHom.comp_assoc,
      counit_comp_C, RingHom.comp_id]
  · rw [map_comp_coproduct_universalStrictCoordinate, tensorLift_comp_map_rightUnit,
      tensorLift_comp_C, map_conjugation_universalStrictCoordinate, FormalCoordinate.map_comp,
      map_counit_universalStrictCoordinate, map_one]
    simp

/-- **The right antipode equation** `μ ∘ (id ⊗ c) ∘ Δ = η_L ∘ ε`. -/
theorem tensorLift_id_conjugation_comp_coproduct :
    (tensorLift p ⟨(RingHom.id _, conjugation p), by
        rw [conjugation_comp_C, RingHom.id_comp]⟩).comp (coproduct p) =
      C.comp counit := by
  refine ringHom_ext_universalStrictCoordinate p ?_ ?_
  · rw [comp_coproduct_comp_C, tensorLift_comp_C, RingHom.comp_assoc, counit_comp_C,
      RingHom.comp_id, RingHom.id_comp]
  · rw [map_comp_coproduct_universalStrictCoordinate, tensorLift_comp_map_rightUnit,
      tensorLift_comp_C, map_conjugation_universalStrictCoordinate, FormalCoordinate.map_comp,
      map_counit_universalStrictCoordinate, map_one]
    simp

/-! ### Morphism from the Lazard Hopf algebroid `(L, L[b₁, b₂, …])` -/

/-- The canonical ring homomorphism `L →+* ℤ[v₁, v₂, …]` classifying
`universalHazewinkelIntegralFormalGroup p`. -/
def ofLazardRing : LazardRing →+* MvPolynomial ℕ+ ℤ :=
  LazardRing.lift ⟨universalHazewinkelIntegralFormalGroup p, inferInstance⟩

@[simp]
theorem map_ofLazardRing :
    LazardRing.formalGroup.map (ofLazardRing p) = universalHazewinkelIntegralFormalGroup p :=
  LazardRing.map_lift _

/-- The canonical ring homomorphism `L[b₁, b₂, …] →+* ℤ[v₁, v₂, …][t₁, t₂, …]` classifying the
universal Hazewinkel formal group law together with `universalStrictCoordinate p`. -/
def ofLazardCoordinateChange :
    MvPolynomial ℕ+ LazardRing →+* MvPolynomial ℕ+ (MvPolynomial ℕ+ ℤ) :=
  LazardRing.coordinateChangeLift
    (⟨(universalHazewinkelIntegralFormalGroup p).map C, inferInstance⟩,
      ⟨universalStrictCoordinate p, universalStrictCoordinate_mem_ker p⟩)

/-- `ofLazardCoordinateChange p` specializes the universal strict coordinate over `L[b₁, b₂, …]` to
`universalStrictCoordinate p`. -/
@[simp]
theorem map_ofLazardCoordinateChange_universalStrictCoordinate :
    FormalCoordinate.map (ofLazardCoordinateChange p) FormalCoordinate.universalStrictCoordinate =
      universalStrictCoordinate p :=
  LazardRing.map_coordinateChangeLift_universalStrictCoordinate _

/-- Compatibility of `(ofLazardRing p, ofLazardCoordinateChange p)` with the left units. -/
@[simp]
theorem ofLazardCoordinateChange_comp_C :
    (ofLazardCoordinateChange p).comp C = C.comp (ofLazardRing p) :=
  LazardRing.hom_ext <| by
    rw [ofLazardCoordinateChange, LazardRing.coordinateChangeLift_comp_C, LazardRing.map_lift,
      ← FormalGroup.map_comp, map_ofLazardRing]

/-- Compatibility of `(ofLazardRing p, ofLazardCoordinateChange p)` with the right units. -/
@[simp]
theorem ofLazardCoordinateChange_comp_rightUnit :
    (ofLazardCoordinateChange p).comp LazardRing.rightUnit =
      (rightUnit p).comp (ofLazardRing p) :=
  LazardRing.hom_ext <| by
    rw [LazardRing.map_comp_rightUnit, map_ofLazardCoordinateChange_universalStrictCoordinate,
      ofLazardCoordinateChange_comp_C, ← FormalGroup.map_comp, map_ofLazardRing, ← map_rightUnit,
      ← FormalGroup.map_comp, map_ofLazardRing]

/-- Compatibility of `(ofLazardRing p, ofLazardCoordinateChange p)` with the counits. -/
@[simp]
theorem counit_comp_ofLazardCoordinateChange :
    counit.comp (ofLazardCoordinateChange p) = (ofLazardRing p).comp LazardRing.counit := by
  refine FormalCoordinate.ringHom_ext_universalStrictCoordinate ?_ ?_
  · rw [RingHom.comp_assoc, ofLazardCoordinateChange_comp_C, ← RingHom.comp_assoc,
      counit_comp_C, RingHom.id_comp, RingHom.comp_assoc, LazardRing.counit_comp_C,
      RingHom.comp_id]
  · rw [FormalCoordinate.map_comp, map_ofLazardCoordinateChange_universalStrictCoordinate,
      map_counit_universalStrictCoordinate, FormalCoordinate.map_comp,
      LazardRing.map_counit_universalStrictCoordinate, map_one]

/-- Compatibility of `ofLazardCoordinateChange p` with the coproducts. -/
theorem coproduct_comp_ofLazardCoordinateChange :
    (coproduct p).comp (ofLazardCoordinateChange p) =
      (LazardRing.tensorLift
        (R := MvPolynomial ℕ+ (MvPolynomial ℕ+ (MvPolynomial ℕ+ ℤ)))
        ⟨(C.comp (ofLazardCoordinateChange p),
          (map (rightUnit p)).comp (ofLazardCoordinateChange p)), by
            rw [RingHom.comp_assoc, ofLazardCoordinateChange_comp_rightUnit,
              RingHom.comp_assoc, ofLazardCoordinateChange_comp_C,
              ← RingHom.comp_assoc, ← RingHom.comp_assoc, map_comp_C (rightUnit p)]⟩).comp
        LazardRing.coproduct := by
  refine FormalCoordinate.ringHom_ext_universalStrictCoordinate
    (R := MvPolynomial ℕ+ (MvPolynomial ℕ+ (MvPolynomial ℕ+ ℤ))) ?_ ?_
  · rw [RingHom.comp_assoc, ofLazardCoordinateChange_comp_C, ← RingHom.comp_assoc,
      coproduct_comp_C, LazardRing.comp_coproduct_comp_C, LazardRing.tensorLift_comp_C]
    dsimp only
    rw [RingHom.comp_assoc, RingHom.comp_assoc, ofLazardCoordinateChange_comp_C]
  · rw [FormalCoordinate.map_comp
          (R := MvPolynomial ℕ+ LazardRing)
          (S := MvPolynomial ℕ+ (MvPolynomial ℕ+ ℤ))
          (T := MvPolynomial ℕ+ (MvPolynomial ℕ+ (MvPolynomial ℕ+ ℤ))),
      map_ofLazardCoordinateChange_universalStrictCoordinate,
      map_coproduct_universalStrictCoordinate,
      LazardRing.map_comp_coproduct_universalStrictCoordinate,
      LazardRing.tensorLift_comp_map_rightUnit, LazardRing.tensorLift_comp_C]
    dsimp only
    rw [FormalCoordinate.map_comp
          (R := MvPolynomial ℕ+ LazardRing)
          (S := MvPolynomial ℕ+ (MvPolynomial ℕ+ ℤ))
          (T := MvPolynomial ℕ+ (MvPolynomial ℕ+ (MvPolynomial ℕ+ ℤ))),
      FormalCoordinate.map_comp
          (R := MvPolynomial ℕ+ LazardRing)
          (S := MvPolynomial ℕ+ (MvPolynomial ℕ+ ℤ))
          (T := MvPolynomial ℕ+ (MvPolynomial ℕ+ (MvPolynomial ℕ+ ℤ))),
      map_ofLazardCoordinateChange_universalStrictCoordinate]

/-- Compatibility of `ofLazardCoordinateChange p` with the conjugations. -/
@[simp]
theorem conjugation_comp_ofLazardCoordinateChange :
    (conjugation p).comp (ofLazardCoordinateChange p) =
      (ofLazardCoordinateChange p).comp LazardRing.conjugation := by
  refine FormalCoordinate.ringHom_ext_universalStrictCoordinate ?_ ?_
  · rw [RingHom.comp_assoc, ofLazardCoordinateChange_comp_C, ← RingHom.comp_assoc,
      conjugation_comp_C, RingHom.comp_assoc, LazardRing.conjugation_comp_C,
      ofLazardCoordinateChange_comp_rightUnit]
  · rw [FormalCoordinate.map_comp, map_ofLazardCoordinateChange_universalStrictCoordinate,
      map_conjugation_universalStrictCoordinate, FormalCoordinate.map_comp,
      LazardRing.map_conjugation_universalStrictCoordinate, map_inv,
      map_ofLazardCoordinateChange_universalStrictCoordinate]

/-! ### Ravenel's logarithm recursion and degree-one formulas -/

/-- **Ravenel's recursion for the right unit**: for any homomorphism `f` from
`ℤ[v₁, v₂, …][t₁, t₂, …]` into a `ℚ`-algebra `K`, the Hazewinkel logarithm coefficients satisfy
`mₙ(f ∘ η_R ∘ X) = mₙ(f ∘ η_L ∘ X) + ∑_{i < n} mᵢ(f ∘ η_L ∘ X) f(t_{n - i})^(pⁱ)`. -/
theorem hazewinkelLogCoeff_comp_rightUnit {K : Type*} [CommRing K] [Algebra ℚ K]
    (f : MvPolynomial ℕ+ (MvPolynomial ℕ+ ℤ) →+* K) (n : ℕ) :
    hazewinkelLogCoeff p (f.comp (rightUnit p) ∘ X) n =
      hazewinkelLogCoeff p (f.comp C ∘ X) n +
        ∑ i ∈ Finset.range n,
          hazewinkelLogCoeff p (f.comp C ∘ X) i * f (X (n - 1 - i).succPNat) ^ p ^ i := by
  have hF := map_comp_rightUnit p f
  rw [map_universalStrictCoordinate, map_universalHazewinkelIntegralFormalGroup,
    map_universalHazewinkelIntegralFormalGroup,
    hazewinkelIntegralFormalGroup_eq_hazewinkelFormalGroup,
    hazewinkelIntegralFormalGroup_eq_hazewinkelFormalGroup] at hF
  have hlog := congrArg (fun G : FormalGroup K ↦ PowerSeries.coeff (p ^ n) G.log) hF
  rwa [log_hazewinkelFormalGroup, coeff_hazewinkelLog_pow _ hp.out.one_lt n,
    log_pTypicalStrictCoordinate_smul_hazewinkelFormalGroup,
    coeff_pow_subst_pTypicalStrictCurve_hazewinkelLog hp.out.one_lt] at hlog

/-- **`η_R(v₁) = v₁ + p t₁`**: explicit formula for the right unit on the first Hazewinkel
generator `v₁ = X 1`. -/
theorem rightUnit_X_one :
    rightUnit p (X 1) = C (X 1) + (p : MvPolynomial ℕ+ (MvPolynomial ℕ+ ℤ)) * X 1 := by
  let ι : MvPolynomial ℕ+ (MvPolynomial ℕ+ ℤ) →+* MvPolynomial ℕ+ (MvPolynomial ℕ+ ℚ) :=
    map (map (Int.castRingHom ℚ))
  have hι : Function.Injective ι := map_injective _ (map_injective _ Int.cast_injective)
  apply hι
  have hrec := hazewinkelLogCoeff_comp_rightUnit p ι 1
  simp only [Finset.range_one, Finset.sum_singleton, hazewinkelLogCoeff_one,
    hazewinkelLogCoeff_zero, Nat.sub_self, pow_zero, pow_one, one_mul, Function.comp_apply,
    RingHom.comp_apply] at hrec
  have hp0 : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.ne_zero
  have hmul := congrArg ((p : ℚ) • ·) hrec
  rw [smul_add, smul_inv_smul₀ hp0, smul_inv_smul₀ hp0] at hmul
  rw [hmul, map_add, map_mul, map_natCast, Nat.cast_smul_eq_nsmul, nsmul_eq_mul]
  rfl

/-- **`Δ(t₁) = t₁ ⊗ 1 + 1 ⊗ t₁`**: `t₁` is primitive in
`(ℤ[v₁, v₂, …], ℤ[v₁, v₂, …][t₁, t₂, …])`. -/
theorem coproduct_X_one : coproduct p (X 1) = C (X 1) + X 1 := by
  let ι : MvPolynomial ℕ+ (MvPolynomial ℕ+ (MvPolynomial ℕ+ ℤ)) →+*
      MvPolynomial ℕ+ (MvPolynomial ℕ+ (MvPolynomial ℕ+ ℚ)) :=
    map (map (map (Int.castRingHom ℚ)))
  have hι : Function.Injective ι :=
    map_injective _ (map_injective _ (map_injective _ Int.cast_injective))
  have hΔ := congrArg (coproduct p) (rightUnit_X_one p)
  rw [coproduct_rightUnit, rightUnit_X_one, map_add, map_C, map_mul, map_natCast, map_X,
    rightUnit_X_one, map_add, map_mul, map_natCast, map_add, coproduct_C, map_mul,
    map_natCast] at hΔ
  have hsub : (p : MvPolynomial ℕ+ (MvPolynomial ℕ+ (MvPolynomial ℕ+ ℤ))) * coproduct p (X 1) =
      (p : MvPolynomial ℕ+ (MvPolynomial ℕ+ (MvPolynomial ℕ+ ℤ))) * (C (X 1) + X 1) := by
    linear_combination -hΔ
  apply hι
  have hQ := congrArg ι hsub
  rw [map_mul, map_mul, map_natCast] at hQ
  have hpu : IsUnit (p : MvPolynomial ℕ+ (MvPolynomial ℕ+ (MvPolynomial ℕ+ ℚ))) := by
    have hpQ : IsUnit (p : ℚ) := isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr hp.out.ne_zero)
    simpa only [map_natCast] using hpQ.map (algebraMap ℚ _)
  exact hpu.mul_left_cancel hQ

/-- **`c(t₁) = -t₁`**: conjugation negates `t₁`. -/
theorem conjugation_X_one : conjugation p (X 1) = -X 1 := by
  let ι : MvPolynomial ℕ+ (MvPolynomial ℕ+ ℤ) →+* MvPolynomial ℕ+ (MvPolynomial ℕ+ ℚ) :=
    map (map (Int.castRingHom ℚ))
  have hι : Function.Injective ι := map_injective _ (map_injective _ Int.cast_injective)
  have hc := congrArg (conjugation p) (rightUnit_X_one p)
  rw [conjugation_rightUnit, map_add, conjugation_C, rightUnit_X_one, map_mul, map_natCast] at hc
  have hsub : (p : MvPolynomial ℕ+ (MvPolynomial ℕ+ ℤ)) * conjugation p (X 1) =
      (p : MvPolynomial ℕ+ (MvPolynomial ℕ+ ℤ)) * (-X 1) := by
    linear_combination -hc
  apply hι
  have hQ := congrArg ι hsub
  rw [map_mul, map_mul, map_natCast] at hQ
  have hpu : IsUnit (p : MvPolynomial ℕ+ (MvPolynomial ℕ+ ℚ)) := by
    have hpQ : IsUnit (p : ℚ) := isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr hp.out.ne_zero)
    simpa only [map_natCast] using hpQ.map (algebraMap ℚ _)
  exact hpu.mul_left_cancel hQ

/-! ### Reduction to Milnor's polynomial dual Steenrod algebra `𝔽_p[t₁, t₂, …]` -/

private theorem hazewinkelLogCoeff_eval_zero_comp_rightUnit (k : ℕ) :
    hazewinkelLogCoeff p
        (((map (Int.castRingHom ℚ)).comp (map (eval (0 : ℕ+ → ℤ)))).comp (rightUnit p) ∘ X) k =
      if k = 0 then 1 else X (k - 1).succPNat := by
  set f : MvPolynomial ℕ+ (MvPolynomial ℕ+ ℤ) →+* MvPolynomial ℕ+ ℚ :=
    (map (Int.castRingHom ℚ)).comp (map (eval (0 : ℕ+ → ℤ)))
  have hf0 : ⇑(f.comp C) ∘ X = (0 : ℕ+ → MvPolynomial ℕ+ ℚ) :=
    funext fun i ↦ by simp [f]
  have h0_succ (m : ℕ) : hazewinkelLogCoeff p (0 : ℕ+ → MvPolynomial ℕ+ ℚ) (m + 1) = 0 := by
    simp [hazewinkelLogCoeff_succ, zero_pow (pow_ne_zero _ hp.out.ne_zero)]
  rcases k with _ | n
  · simp
  · rw [ite_eq_right (Nat.succ_ne_zero n), Nat.add_sub_cancel, hazewinkelLogCoeff_comp_rightUnit,
      hf0, h0_succ n, zero_add, Finset.sum_eq_single 0]
    · simp [f]
    · intro i _ hi0
      obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi0
      rw [h0_succ m, zero_mul]
    · intro h0; exact absurd (Finset.mem_range.mpr (Nat.succ_pos n)) h0

/-- Specializing `vᵢ ↦ 0` in `η_R(v_{n + 1})` satisfies the exact integral recursion
`w₀(n + 1) + ∑_{i < n} t_{i + 1} w₀(n - i)^(p^(i + 1)) = p t_{n + 1}` in `ℤ[t₁, t₂, …]`. -/
theorem map_eval_zero_rightUnit_X_succ (n : ℕ) :
    map (eval (0 : ℕ+ → ℤ)) (rightUnit p (X n.succPNat)) +
        ∑ i ∈ Finset.range n, X i.succPNat *
          map (eval (0 : ℕ+ → ℤ)) (rightUnit p (X (n - 1 - i).succPNat)) ^ p ^ (i + 1) =
      (p : MvPolynomial ℕ+ ℤ) * X n.succPNat := by
  let ι : MvPolynomial ℕ+ ℤ →+* MvPolynomial ℕ+ ℚ := map (Int.castRingHom ℚ)
  apply MvPolynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective
  set wQ : ℕ+ → MvPolynomial ℕ+ ℚ :=
    ((ι.comp (map (eval (0 : ℕ+ → ℤ)))).comp (rightUnit p)) ∘ X
  have hrec := natCast_mul_hazewinkelLogCoeff_succ wQ hp.out.ne_zero n
  rw [Finset.sum_range_succ', hazewinkelLogCoeff_eval_zero_comp_rightUnit p (n + 1),
    ite_eq_right (Nat.succ_ne_zero n), Nat.add_sub_cancel, hazewinkelLogCoeff_zero, pow_zero,
    pow_one, one_mul, Nat.sub_zero, add_comm] at hrec
  have hsum : (∑ i ∈ Finset.range n, hazewinkelLogCoeff p wQ (i + 1) *
      wQ (n - (i + 1)).succPNat ^ p ^ (i + 1)) =
      ∑ i ∈ Finset.range n, X i.succPNat * wQ (n - 1 - i).succPNat ^ p ^ (i + 1) := by
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [hazewinkelLogCoeff_eval_zero_comp_rightUnit p (i + 1), ite_eq_right (Nat.succ_ne_zero i),
      Nat.add_sub_cancel, show n - (i + 1) = n - 1 - i by omega]
  rw [hsum] at hrec
  simpa only [ι, wQ, map_add, map_sum, map_mul, map_pow, map_natCast, map_X,
    Function.comp_apply, RingHom.comp_apply] using hrec.symm

/-- Every `η_R(vᵢ)` becomes divisible by `p` in `ℤ[t₁, t₂, …]` upon specializing `vⱼ ↦ 0`. -/
theorem natCast_dvd_map_eval_zero_rightUnit_X (i : ℕ+) :
    (p : MvPolynomial ℕ+ ℤ) ∣ map (eval (0 : ℕ+ → ℤ)) (rightUnit p (X i)) := by
  suffices ∀ n, ∀ j : ℕ+, (j : ℕ) ≤ n →
      (p : MvPolynomial ℕ+ ℤ) ∣ map (eval (0 : ℕ+ → ℤ)) (rightUnit p (X j)) from
    this (i : ℕ) i le_rfl
  intro n
  induction n with
  | zero => intro j hj; have := j.pos; omega
  | succ n ih =>
    intro j hj
    rcases lt_or_eq_of_le hj with hlt | heq
    · exact ih j (Nat.lt_succ_iff.mp hlt)
    · obtain rfl : j = n.succPNat := PNat.coe_injective heq
      have hrec := map_eval_zero_rightUnit_X_succ p n
      have hdvd_sum : (p : MvPolynomial ℕ+ ℤ) ∣
          ∑ k ∈ Finset.range n, X k.succPNat *
            map (eval (0 : ℕ+ → ℤ)) (rightUnit p (X (n - 1 - k).succPNat)) ^ p ^ (k + 1) := by
        refine Finset.dvd_sum fun k hk ↦ dvd_mul_of_dvd_right ?_ _
        rw [Finset.mem_range] at hk
        exact dvd_pow (ih (n - 1 - k).succPNat (by simp; omega)) (pow_ne_zero _ hp.out.ne_zero)
      have heq' : map (eval (0 : ℕ+ → ℤ)) (rightUnit p (X n.succPNat)) =
          (p : MvPolynomial ℕ+ ℤ) * X n.succPNat -
            ∑ k ∈ Finset.range n, X k.succPNat *
              map (eval (0 : ℕ+ → ℤ)) (rightUnit p (X (n - 1 - k).succPNat)) ^ p ^ (k + 1) := by
        linear_combination hrec
      rw [heq']
      exact dvd_sub (dvd_mul_right _ _) hdvd_sum

/-- Specializing `vᵢ ↦ 0` on the left factor of `Δ(t_{n + 1})` yields the exact integral polynomial
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
  have hF_inj : Function.Injective (map ιQ : MvPolynomial ℕ+ (MvPolynomial ℕ+ ℤ) →+* _) :=
    map_injective _ (map_injective _ Int.cast_injective)
  have h0_succ (m : ℕ) :
      hazewinkelLogCoeff p (0 : ℕ+ → MvPolynomial ℕ+ (MvPolynomial ℕ+ ℚ)) (m + 1) = 0 := by
    simp [hazewinkelLogCoeff_succ, zero_pow (pow_ne_zero _ hp.out.ne_zero)]
  apply hF_inj
  have hA : hazewinkelLogCoeff p ((F.comp (coproduct p)).comp (rightUnit p) ∘ X) (n + 1) =
      map ιQ (map ev0 (coproduct p (X n.succPNat))) := by
    have hC0 : ⇑((F.comp (coproduct p)).comp C) ∘ X = 0 :=
      funext fun i ↦ by simp [F, ev0, ιQ]
    rw [hazewinkelLogCoeff_comp_rightUnit, hC0, h0_succ n, zero_add, Finset.sum_eq_single 0]
    · simp [F]
    · intro i _ hi0
      obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi0
      rw [h0_succ m, zero_mul]
    · intro h0; exact absurd (Finset.mem_range.mpr (Nat.succ_pos n)) h0
  have hB : hazewinkelLogCoeff p
      ((F.comp (map (rightUnit p))).comp (rightUnit p) ∘ X) (n + 1) =
      C (X n.succPNat) + X n.succPNat +
        ∑ i ∈ Finset.range n, C (X i.succPNat) * X (n - 1 - i).succPNat ^ p ^ (i + 1) := by
    set w0Q : ℕ+ → MvPolynomial ℕ+ ℚ := ((ιQ.comp ev0).comp (rightUnit p)) ∘ X
    have hFC : ⇑((F.comp (map (rightUnit p))).comp C) ∘ X = CQ ∘ w0Q :=
      funext fun i ↦ by simp [F, ev0, ιQ, CQ, w0Q]
    have hFX : ∀ k : ℕ+, (F.comp (map (rightUnit p))) (X k) = X k := fun k ↦ by simp [F, ev0, ιQ]
    rw [hazewinkelLogCoeff_comp_rightUnit, hFC, ← map_hazewinkelLogCoeff w0Q CQ,
      hazewinkelLogCoeff_eval_zero_comp_rightUnit p (n + 1), ite_eq_right (Nat.succ_ne_zero n),
      Nat.add_sub_cancel, Finset.sum_range_succ', ← map_hazewinkelLogCoeff w0Q CQ,
      hazewinkelLogCoeff_zero, map_one, one_mul, pow_zero, pow_one, Nat.sub_zero, hFX]
    have hsum : (∑ i ∈ Finset.range n,
        hazewinkelLogCoeff p (CQ ∘ w0Q) (i + 1) *
          (F.comp (map (rightUnit p))) (X (n - (i + 1)).succPNat) ^ p ^ (i + 1)) =
        ∑ i ∈ Finset.range n, C (X i.succPNat) * X (n - 1 - i).succPNat ^ p ^ (i + 1) := by
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [← map_hazewinkelLogCoeff w0Q CQ, hazewinkelLogCoeff_eval_zero_comp_rightUnit p (i + 1),
        ite_eq_right (Nat.succ_ne_zero i), Nat.add_sub_cancel, hFX,
        show n - (i + 1) = n - 1 - i by omega]
    rw [hsum]
    ring
  have hEq : (F.comp (coproduct p)).comp (rightUnit p) =
      (F.comp (map (rightUnit p))).comp (rightUnit p) := by
    rw [RingHom.comp_assoc, coproduct_comp_rightUnit, ← RingHom.comp_assoc]
  rw [← hA, hEq, hB]
  simp [ιQ, map_add, map_sum, map_mul, map_pow, map_C, map_X]

/-- **The quotient map to Milnor's polynomial dual Steenrod algebra**
`ℤ[v₁, v₂, …][t₁, t₂, …] →+* 𝔽_p[t₁, t₂, …]`, killing `(p, v₁, v₂, …)` and sending `tᵢ ↦ tᵢ`. -/
def milnorQuotient :
    MvPolynomial ℕ+ (MvPolynomial ℕ+ ℤ) →+* MvPolynomial ℕ+ (ZMod p) :=
  map ((Int.castRingHom (ZMod p)).comp (eval (0 : ℕ+ → ℤ)))

@[simp]
theorem milnorQuotient_X (i : ℕ+) : milnorQuotient p (X i) = X i := by
  simp [milnorQuotient]

@[simp]
theorem milnorQuotient_C_X (i : ℕ+) : milnorQuotient p (C (X i)) = 0 := by
  simp [milnorQuotient]

/-- `milnorQuotient p` is surjective onto `𝔽_p[t₁, t₂, …]`. -/
theorem milnorQuotient_surjective : Function.Surjective (milnorQuotient p) := by
  have hcomp : (milnorQuotient p).comp (map (C : ℤ →+* MvPolynomial ℕ+ ℤ)) =
      map (Int.castRingHom (ZMod p)) := by
    refine ringHom_ext' (RingHom.ext_int _ _) fun i ↦ ?_
    simp [milnorQuotient]
  intro q
  obtain ⟨qZ, hqZ⟩ := map_surjective (Int.castRingHom (ZMod p)) ZMod.intCast_surjective q
  exact ⟨map C qZ, by simpa [← RingHom.comp_apply, hcomp] using hqZ⟩

@[simp]
theorem milnorQuotient_rightUnit_X (i : ℕ+) : milnorQuotient p (rightUnit p (X i)) = 0 := by
  have hfact : milnorQuotient p =
      (map (Int.castRingHom (ZMod p))).comp (map (eval (0 : ℕ+ → ℤ))) :=
    RingHom.ext fun q ↦ (map_map _ _ q).symm
  obtain ⟨u, hu⟩ := natCast_dvd_map_eval_zero_rightUnit_X p i
  rw [hfact, RingHom.comp_apply, hu, map_mul, map_natCast, CharP.cast_eq_zero, zero_mul]

/-- **Both units agree modulo `(p, v₁, v₂, …)`**:
`(milnorQuotient p) ∘ η_R = (milnorQuotient p) ∘ η_L`. -/
@[simp]
theorem milnorQuotient_comp_rightUnit :
    (milnorQuotient p).comp (rightUnit p) = (milnorQuotient p).comp C :=
  MvPolynomial.homEquiv.injective <| funext fun i ↦ by
    simp [MvPolynomial.homEquiv]

/-- **The ideal `(p, v₁, v₂, …)` is an invariant ideal** of
`(ℤ[v₁, v₂, …], ℤ[v₁, v₂, …][t₁, t₂, …])`: its extensions along `η_R` and `η_L = C` coincide. -/
theorem map_rightUnit_ker_eval_zero_mod :
    (RingHom.ker ((Int.castRingHom (ZMod p)).comp (eval (0 : ℕ+ → ℤ)))).map (rightUnit p) =
      (RingHom.ker ((Int.castRingHom (ZMod p)).comp (eval (0 : ℕ+ → ℤ)))).map C := by
  have hle :
      (RingHom.ker ((Int.castRingHom (ZMod p)).comp (eval (0 : ℕ+ → ℤ)))).map (rightUnit p) ≤
        (RingHom.ker ((Int.castRingHom (ZMod p)).comp (eval (0 : ℕ+ → ℤ)))).map C := by
    rw [← ker_map, ← milnorQuotient, Ideal.map_le_iff_le_comap]
    intro a ha
    have hEq : milnorQuotient p (rightUnit p a) = milnorQuotient p (C a) :=
      RingHom.congr_fun (milnorQuotient_comp_rightUnit p) a
    rw [Ideal.mem_comap, RingHom.mem_ker, hEq, milnorQuotient, map_C, RingHom.mem_ker.mp ha,
      map_zero]
  refine le_antisymm hle ?_
  have h' := Ideal.map_mono (f := conjugation p) hle
  rwa [Ideal.map_map, Ideal.map_map, conjugation_comp_rightUnit, conjugation_comp_C] at h'

/-- **Milnor's coproduct** on the polynomial dual Steenrod algebra `𝔽_p[t₁, t₂, …]`:
`Δ(t_{n + 1}) = t_{n + 1} ⊗ 1 + 1 ⊗ t_{n + 1} + ∑_{i < n} t_{i + 1} ⊗ t_{n - i}^(p^(i + 1))`. -/
def milnorCoproduct :
    MvPolynomial ℕ+ (ZMod p) →ₐ[ZMod p] MvPolynomial ℕ+ (MvPolynomial ℕ+ (ZMod p)) :=
  MvPolynomial.aeval fun i ↦
    C (X i) + X i +
      ∑ r ∈ Finset.range i.natPred,
        C (X r.succPNat) * X (i.natPred - 1 - r).succPNat ^ p ^ (r + 1)

@[simp]
theorem milnorCoproduct_X_succ (n : ℕ) :
    milnorCoproduct p (X n.succPNat) =
      C (X n.succPNat) + X n.succPNat +
        ∑ r ∈ Finset.range n, C (X r.succPNat) * X (n - 1 - r).succPNat ^ p ^ (r + 1) := by
  simp [milnorCoproduct, Nat.natPred_succPNat]

/-- **`milnorCoproduct p` is the reduction of `coproduct p` along `milnorQuotient p`.** -/
theorem milnorCoproduct_comp_milnorQuotient :
    (milnorCoproduct p).toRingHom.comp (milnorQuotient p) =
      (map (milnorQuotient p)).comp (coproduct p) := by
  refine ringHom_ext' ?_ fun i ↦ ?_
  · apply MvPolynomial.homEquiv.injective
    funext j
    simp [MvPolynomial.homEquiv]
  · obtain ⟨n, rfl⟩ : ∃ n, n.succPNat = i := ⟨i.natPred, i.succPNat_natPred⟩
    have hmq : milnorQuotient p =
        (map (Int.castRingHom (ZMod p))).comp (map (eval (0 : ℕ+ → ℤ))) :=
      RingHom.ext fun q ↦ (map_map _ _ q).symm
    have hfact : map (σ := ℕ+) (milnorQuotient p) =
        (map (map (Int.castRingHom (ZMod p)))).comp (map (map (eval (0 : ℕ+ → ℤ)))) := by
      rw [hmq]
      exact RingHom.ext fun q ↦ (map_map _ _ q).symm
    rw [RingHom.comp_apply, milnorQuotient_X, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
      milnorCoproduct_X_succ, RingHom.comp_apply, hfact, RingHom.comp_apply,
      map_map_eval_zero_coproduct_X_succ]
    simp [map_add, map_sum, map_mul, map_pow, map_C, map_X]

/-- **Milnor's conjugation (antipode)** on `𝔽_p[t₁, t₂, …]`, induced by `conjugation p`. -/
def milnorConjugation :
    MvPolynomial ℕ+ (ZMod p) →ₐ[ZMod p] MvPolynomial ℕ+ (ZMod p) :=
  MvPolynomial.aeval fun i ↦ milnorQuotient p (conjugation p (X i))

@[simp]
theorem milnorConjugation_X_eq (i : ℕ+) :
    milnorConjugation p (X i) = milnorQuotient p (conjugation p (X i)) :=
  aeval_X _ i

/-- **`milnorConjugation p` is the reduction of `conjugation p` along `milnorQuotient p`.** -/
theorem milnorConjugation_comp_milnorQuotient :
    (milnorConjugation p).toRingHom.comp (milnorQuotient p) =
      (milnorQuotient p).comp (conjugation p) := by
  refine ringHom_ext' ?_ fun i ↦ by simp
  apply MvPolynomial.homEquiv.injective
  funext j
  simp [MvPolynomial.homEquiv]

/-- `milnorConjugation p` is an involution on `𝔽_p[t₁, t₂, …]`. -/
@[simp]
theorem milnorConjugation_comp_milnorConjugation :
    (milnorConjugation p).comp (milnorConjugation p) =
      AlgHom.id (ZMod p) (MvPolynomial ℕ+ (ZMod p)) := by
  refine MvPolynomial.algHom_ext fun i ↦ ?_
  have h : milnorConjugation p (milnorQuotient p (conjugation p (X i))) =
      milnorQuotient p (conjugation p (conjugation p (X i))) :=
    RingHom.congr_fun (milnorConjugation_comp_milnorQuotient p) (conjugation p (X i))
  rw [AlgHom.comp_apply, milnorConjugation_X_eq, h, conjugation_conjugation, milnorQuotient_X,
    AlgHom.id_apply]

@[simp]
theorem milnorConjugation_conjugation (x : MvPolynomial ℕ+ (ZMod p)) :
    milnorConjugation p (milnorConjugation p x) = x :=
  AlgHom.congr_fun (milnorConjugation_comp_milnorConjugation p) x

/-- **Milnor's recursive antipode formula** on `𝔽_p[t₁, t₂, …]`:
`c(t_{n + 1}) = -t_{n + 1} - ∑_{i < n} t_{i + 1} c(t_{n - i})^(p^(i + 1))`. -/
theorem milnorConjugation_X_succ (n : ℕ) :
    milnorConjugation p (X n.succPNat) =
      -X n.succPNat -
        ∑ r ∈ Finset.range n,
          X r.succPNat * milnorConjugation p (X (n - 1 - r).succPNat) ^ p ^ (r + 1) := by
  let μc : MvPolynomial ℕ+ (MvPolynomial ℕ+ (ZMod p)) →+* MvPolynomial ℕ+ (ZMod p) :=
    eval₂Hom (RingHom.id _) (milnorConjugation p ∘ X)
  have hcomm : μc.comp (map (milnorQuotient p)) =
      (milnorQuotient p).comp
        (tensorLift p ⟨(RingHom.id _, conjugation p), by
          rw [conjugation_comp_C, RingHom.id_comp]⟩) := by
    refine ringHom_ext' (RingHom.ext fun x ↦ by simp [μc]) fun i ↦ ?_
    simp [μc]
  have hanti := congrArg (milnorQuotient p)
    (RingHom.congr_fun (tensorLift_id_conjugation_comp_coproduct p) (X n.succPNat))
  rw [RingHom.comp_apply, ← RingHom.comp_apply (milnorQuotient p), ← hcomm, RingHom.comp_apply,
    ← RingHom.comp_apply (map (milnorQuotient p)), ← milnorCoproduct_comp_milnorQuotient,
    RingHom.comp_apply, milnorQuotient_X, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
    milnorCoproduct_X_succ, RingHom.comp_apply, counit_X, map_zero, map_zero] at hanti
  simp only [μc, map_add, map_sum, map_mul, map_pow, eval₂Hom_C, RingHom.id_apply, eval₂Hom_X',
    Function.comp_apply] at hanti
  linear_combination hanti

end Hazewinkel

end TauCeti
