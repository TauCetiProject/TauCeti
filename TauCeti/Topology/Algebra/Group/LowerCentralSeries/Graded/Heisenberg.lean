/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.Transgression
public import TauCeti.Topology.Algebra.Group.LowerCentralSeries.Graded.Span

/-!
# The functional on `gr_1(G)` of a Heisenberg cochain

Let `G` be a topological group, let `M`, `A` and `P` be `G`-modules with a pairing
`μ : M →+ A →+ P`, let `a : G → M` and `b : G → A` be continuous `1`-cocycles and let `h : G → P`
be a Heisenberg cochain for `(a, b)` (`TauCeti.ContCohomology.IsHeisenbergCochain`), so that
`h (g * g') = h g + g • h g' + μ (a g) (g • b g')`.

Suppose that the action on `P` is trivial, that `a` and `b` vanish on the first term `λ_1(G)` of
the lower `p`-series, which is automatic for trivial actions when `M` and `A` are killed by `p`
(`TauCeti.ContCohomology.apply_eq_zero_of_mem_Z1_of_mem_pLowerCentralSeries_one`), and that `P`
is killed by `p`. Then the Heisenberg law makes `h` a continuous homomorphism on
`λ_1(G)`, and its values on the `p`-th powers and on the commutators with `G` vanish, so `h`
descends to an additive functional

  `gr_1(G) = λ_1(G) ⧸ λ_2(G) →+ P`,

the **graded restriction** `TauCeti.ContCohomology.IsHeisenbergCochain.gradedRestrict` of `h`. When
the actions on `M` and `A` are trivial as well, its values on the two kinds of elements spanning
`gr_1(G)` are the two components of the cup pairing of `a` and `b`:

* on a bracket `[x, y]` of degree-zero classes, the antisymmetric part
  `μ (a x) (b y) - μ (a y) (b x)`;
* on a `p`-th power `π x`, the diagonal value `(p choose 2) • μ (a x) (b x)`, which vanishes for
  odd `p` and is `μ (a x) (b x)` for `p = 2`.

By the transgression formula of
`TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.Transgression`, the class of `-h|_N`
for a closed normal `N ≤ λ_1(G)` transgresses to the cup product of the descended cocycles, and
`TauCeti.ContCohomology.IsHeisenbergCochain.negRestrict_apply_eq_neg_gradedRestrict_gradedMk`
records that this cocycle is `-gradedRestrict` composed with the projection `N → gr_1(G)`. The
graded restriction is thus the `gr_1`-side input to Labute's Proposition 3, which reads the cup
product of a pro-`p` group off the class of a relator in `gr_1` of the free group; that
identification is not carried out here.

## Main definitions

* `TauCeti.ContCohomology.IsHeisenbergCochain.gradedRestrict`: the functional `gr_1(G) →+ P`
  induced by a Heisenberg cochain.

## Main results

* `TauCeti.ContCohomology.apply_eq_zero_of_mem_Z1_of_mem_pLowerCentralSeries_one`: a continuous
  `1`-cocycle for a trivial action on a group killed by `p` vanishes on `λ_1(G)`.
* `TauCeti.ContCohomology.IsHeisenbergCochain.gradedRestrict_gradedMk`: the defining equation
  `gradedRestrict (gradedMk n) = h n`.
* `TauCeti.ContCohomology.IsHeisenbergCochain.gradedRestrict_gradedBracket_gradedMkZero`,
  `TauCeti.ContCohomology.IsHeisenbergCochain.gradedRestrict_gradedPow_gradedMkZero`: the values
  on brackets and on `p`-th powers of degree-zero classes.
* `TauCeti.ContCohomology.IsHeisenbergCochain.negRestrict_apply_eq_neg_gradedRestrict_gradedMk`:
  the cocycle `-h|_{λ_1}` of the transgression formula is `-gradedRestrict` on classes.

## References

* J. P. Labute, *Classification of Demushkin groups*, Canad. J. Math. 19 (1967), 106–132, §1.4
  and Proposition 3.
* J. Neukirch, A. Schmidt and K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Chapter III,
  §9.
-/

public section

namespace TauCeti.ContCohomology

open Subgroup
open scoped commutatorElement

universe uG uM uA uP

section Cocycle

variable {p : ℕ} {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {M : Type uM} [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M] [T1Space M]
  [DistribMulAction G M]

/-- **Cocycles for a trivial action on a group killed by `p` vanish on `λ_1(G)`.** A continuous
`1`-cocycle for a trivial action is a continuous homomorphism, and its kernel is closed and contains
the `p`-th powers and the commutators. -/
theorem apply_eq_zero_of_mem_Z1_of_mem_pLowerCentralSeries_one
    (htriv : ∀ (g : G) (m : M), g • m = m) (hpM : ∀ m : M, p • m = 0) {f : G → M}
    (hf : f ∈ Z1 G M) {g : G} (hg : g ∈ pLowerCentralSeries p G 1) : f g = 0 := by
  let φ := Additive.toMul (Z1EquivOfSmulEqSelf htriv ⟨f, hf⟩)
  have hφ : ∀ x : G, φ x = Multiplicative.ofAdd (f x) := fun x ↦
    Z1EquivOfSmulEqSelf_apply htriv ⟨f, hf⟩ x
  have hker : IsClosed (φ.toMonoidHom.ker : Set G) := by
    have : (φ.toMonoidHom.ker : Set G) = f ⁻¹' {0} := by
      ext x
      rw [SetLike.mem_coe, MonoidHom.mem_ker, ContinuousMonoidHom.coe_toMonoidHom,
        MonoidHom.coe_ofClass, hφ, ofAdd_eq_one, Set.mem_preimage, Set.mem_singleton_iff]
    rw [this]
    exact isClosed_singleton.preimage (mem_Z1_iff.1 hf).1
  have h := φ.toMonoidHom.pLowerCentralSeries_one_le_ker hker (fun x ↦ by
    rw [ContinuousMonoidHom.coe_toMonoidHom, MonoidHom.coe_ofClass, hφ, ← ofAdd_nsmul, hpM,
      ofAdd_zero]) hg
  rwa [MonoidHom.mem_ker, ContinuousMonoidHom.coe_toMonoidHom, MonoidHom.coe_ofClass, hφ,
    ofAdd_eq_one] at h

end Cocycle

section GradedRestrict

variable {p : ℕ} {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {M : Type uM} [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    [DistribMulAction G M]
  {A : Type uA} [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
    [DistribMulAction G A]
  {P : Type uP} [AddCommGroup P] [TopologicalSpace P] [T1Space P] [DistribMulAction G P]
  {μ : M →+ A →+ P} {a : Z1 G M} {b : Z1 G A} {h : G → P} (hh : IsHeisenbergCochain μ a b h)
  (htrivP : ∀ (g : G) (x : P), g • x = x)
  (haN : ∀ n : pLowerCentralSeries p G 1, (a : G → M) n = 0)
  (hbN : ∀ n : pLowerCentralSeries p G 1, (b : G → A) n = 0)
  (hP : ∀ x : P, p • x = 0)

namespace IsHeisenbergCochain

/-- The restriction of a Heisenberg cochain to `λ_1(G)`, as a homomorphism to `Multiplicative P`:
the action on `P` is trivial, and the cup term of the Heisenberg law vanishes on `λ_1(G)` because
`a` does. -/
private def restrictAux : pLowerCentralSeries p G 1 →* Multiplicative P where
  toFun n := Multiplicative.ofAdd (h n)
  map_one' := by rw [OneMemClass.coe_one, hh.apply_one, ofAdd_zero]
  map_mul' n n' := by
    rw [coe_mul, hh.apply_mul, htrivP, haN n, map_zero, AddMonoidHom.zero_apply, add_zero,
      ofAdd_add]

omit [T1Space P] in
private theorem restrictAux_apply (n : pLowerCentralSeries p G 1) :
    restrictAux hh htrivP haN n = Multiplicative.ofAdd (h n) :=
  rfl

include hh htrivP haN hbN hP in
/-- The restriction of a Heisenberg cochain to `λ_1(G)` kills `λ_2(G)`: it kills the `p`-th
powers because `P` is killed by `p`, and it is conjugation-invariant because `a` and `b` vanish on
`λ_1(G)`. -/
private theorem subgroupOf_le_ker_restrictAux :
    (pLowerCentralSeries p G (1 + 1)).subgroupOf (pLowerCentralSeries p G 1) ≤
      (restrictAux hh htrivP haN).ker := by
  have hker :
      IsClosed ((restrictAux hh htrivP haN).ker : Set (pLowerCentralSeries p G 1)) := by
    have : ((restrictAux hh htrivP haN).ker : Set (pLowerCentralSeries p G 1)) =
        (fun n : pLowerCentralSeries p G 1 ↦ h n) ⁻¹' {0} := by
      ext n
      rw [SetLike.mem_coe, MonoidHom.mem_ker, restrictAux_apply, ofAdd_eq_one, Set.mem_preimage,
        Set.mem_singleton_iff]
    rw [this]
    exact isClosed_singleton.preimage (hh.continuous.comp continuous_subtype_val)
  rw [pLowerCentralSeries_succ p G 1]
  refine (pLowerCentralStep_subgroupOf_le_ker_iff (isClosed_pLowerCentralSeries 1) _ hker).mpr
    ⟨fun n ↦ ?_, fun g n ↦ ?_⟩
  · rw [restrictAux_apply, ← ofAdd_nsmul, hP, ofAdd_zero]
  · rw [restrictAux_apply, restrictAux_apply, MulAut.conjNormal_apply]
    have e := hh.apply_conj haN hbN g⁻¹ n
    rw [inv_inv, htrivP, htrivP, add_sub_cancel_right] at e
    rw [e]

/-- **The graded restriction of a Heisenberg cochain.** For a Heisenberg cochain `h` of the
cocycles `a` and `b`, with trivial action on `P`, `a` and `b` vanishing on `λ_1(G)` and `P` killed
by `p`, the restriction of `h` to `λ_1(G)` is a continuous homomorphism killing `λ_2(G)`, and this
is the additive functional it induces on `gr_1(G) = λ_1(G) ⧸ λ_2(G)`. Its defining equation is
`TauCeti.ContCohomology.IsHeisenbergCochain.gradedRestrict_gradedMk`, and when the actions on `M`
and `A` are trivial as well, its values on brackets and `p`-th powers of degree-zero classes are the
two components of the cup pairing of `a` and `b`
(`TauCeti.ContCohomology.IsHeisenbergCochain.gradedRestrict_gradedBracket_gradedMkZero`,
`TauCeti.ContCohomology.IsHeisenbergCochain.gradedRestrict_gradedPow_gradedMkZero`). -/
def gradedRestrict : gradedPiece p G 1 →+ P :=
  MonoidHom.toAdditiveLeft (QuotientGroup.lift _ (restrictAux hh htrivP haN)
    (subgroupOf_le_ker_restrictAux hh htrivP haN hbN hP))

/-- **The graded restriction on classes**: the defining equation of
`TauCeti.ContCohomology.IsHeisenbergCochain.gradedRestrict`. -/
@[simp]
theorem gradedRestrict_gradedMk (n : pLowerCentralSeries p G 1) :
    hh.gradedRestrict htrivP haN hbN hP (gradedMk p G 1 n) = h n := by
  rw [gradedRestrict, gradedMk_def, MonoidHom.toAdditiveLeft_apply_apply, toMul_ofMul,
    QuotientGroup.lift_mk, restrictAux_apply, toAdd_ofAdd]

variable [IsTopologicalAddGroup P] in
/-- The cocycle `-h|_{λ_1(G)}` of the transgression formula is `-gradedRestrict` on classes. -/
theorem negRestrict_apply_eq_neg_gradedRestrict_gradedMk (n : pLowerCentralSeries p G 1) :
    (hh.negRestrict haN hbN : pLowerCentralSeries p G 1 → P) n =
      -hh.gradedRestrict htrivP haN hbN hP (gradedMk p G 1 n) := by
  rw [coe_negRestrict, gradedRestrict_gradedMk]

variable (htrivM : ∀ (g : G) (m : M), g • m = m) (htrivA : ∀ (g : G) (x : A), g • x = x)
include htrivM htrivA

/-- **The graded restriction on a bracket** of degree-zero classes is the antisymmetric part of
the cup pairing: `[x, y] ↦ μ (a x) (b y) - μ (a y) (b x)`. -/
theorem gradedRestrict_gradedBracket_gradedMkZero (g g' : G) :
    hh.gradedRestrict htrivP haN hbN hP
        (gradedBracket p G 0 0 (gradedMkZero p G g) (gradedMkZero p G g')) =
      μ ((a : G → M) g) ((b : G → A) g') - μ ((a : G → M) g') ((b : G → A) g) := by
  rw [gradedBracket_gradedMkZero, gradedRestrict_gradedMk, coe_mk,
    hh.apply_commutatorElement_of_smul_eq_self htrivM htrivA htrivP]

/-- **The graded restriction on a `p`-th power** of a degree-zero class is the diagonal value of
the cup pairing, weighted by `p choose 2`: `π x ↦ (p choose 2) • μ (a x) (b x)`. -/
theorem gradedRestrict_gradedPow_gradedMkZero (g : G) :
    hh.gradedRestrict htrivP haN hbN hP (gradedPow p G 0 (gradedMkZero p G g)) =
      p.choose 2 • μ ((a : G → M) g) ((b : G → A) g) := by
  rw [gradedPow_gradedMkZero, gradedRestrict_gradedMk, coe_mk,
    hh.apply_pow_of_smul_eq_self htrivM htrivA htrivP, hP, zero_add]

/-- For odd `p`, the graded restriction vanishes on the `p`-th powers of degree-zero classes:
`p` divides `p choose 2`, and `P` is killed by `p`. -/
theorem gradedRestrict_gradedPow_gradedMkZero_of_odd (hp : Odd p) (g : G) :
    hh.gradedRestrict htrivP haN hbN hP (gradedPow p G 0 (gradedMkZero p G g)) = 0 := by
  rw [gradedRestrict_gradedPow_gradedMkZero hh htrivP haN hbN hP htrivM htrivA,
    Nat.choose_two_right, Nat.mul_div_assoc _ (Nat.Odd.sub_odd hp odd_one).two_dvd, mul_nsmul, hP,
    nsmul_zero]

/-- For `p = 2`, the graded restriction on the square of a degree-zero class is the diagonal value
`μ (a x) (b x)` of the cup pairing. -/
theorem gradedRestrict_gradedPow_gradedMkZero_of_two (hp : p = 2) (g : G) :
    hh.gradedRestrict htrivP haN hbN hP (gradedPow p G 0 (gradedMkZero p G g)) =
      μ ((a : G → M) g) ((b : G → A) g) := by
  rw [gradedRestrict_gradedPow_gradedMkZero hh htrivP haN hbN hP htrivM htrivA, hp,
    Nat.choose_self, one_nsmul]

section DegreeOneFamily

variable {ι : Type*} [LT ι] (y : ι → G)

/-- **The graded restriction on the `p`-power members of a degree-one family**:
`π (y i) ↦ (p choose 2) • μ (a (y i)) (b (y i))`. -/
theorem gradedRestrict_degreeOneFamily_inl (i : ι) :
    hh.gradedRestrict htrivP haN hbN hP (degreeOneFamily p y (Sum.inl i)) =
      p.choose 2 • μ ((a : G → M) (y i)) ((b : G → A) (y i)) := by
  rw [degreeOneFamily_inl,
    gradedRestrict_gradedPow_gradedMkZero hh htrivP haN hbN hP htrivM htrivA]

/-- **The graded restriction on the bracket members of a degree-one family**:
`[y i, y j] ↦ μ (a (y i)) (b (y j)) - μ (a (y j)) (b (y i))`. -/
theorem gradedRestrict_degreeOneFamily_inr (ij : {ij : ι × ι // ij.1 < ij.2}) :
    hh.gradedRestrict htrivP haN hbN hP (degreeOneFamily p y (Sum.inr ij)) =
      μ ((a : G → M) (y ij.1.1)) ((b : G → A) (y ij.1.2)) -
        μ ((a : G → M) (y ij.1.2)) ((b : G → A) (y ij.1.1)) := by
  rw [degreeOneFamily_inr,
    gradedRestrict_gradedBracket_gradedMkZero hh htrivP haN hbN hP htrivM htrivA]

end DegreeOneFamily

end IsHeisenbergCochain

end GradedRestrict

end TauCeti.ContCohomology
