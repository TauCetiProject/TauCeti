/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.ConstantExtension.Algebraic
public import TauCeti.FieldTheory.FunctionField.ConstantExtension.Degree
public import TauCeti.FieldTheory.FunctionField.ConstantExtension.RiemannRoch
public import TauCeti.FieldTheory.FunctionField.Differential.CanonicalDivisor
public import TauCeti.FieldTheory.FunctionField.RiemannRoch.DegreeZero

/-!
# The genus under a constant field extension

Let `F' = F · k'` be a separable algebraic constant field extension of an algebraic function
field `F / k` with exact constant field `k`.  The genus of `F' / k'` is the genus of `F / k`, also
when `k' / k` is infinite, for instance an algebraic closure of a perfect `k`.  Riemann's theorem
reads the genus off the multiples `l B` of the pole divisor `B` of a transcendental `x ∈ F`: their
degrees `l [F : k(x)]` and their dimensions do not change in `F'`
(`TauCeti.Divisor.dim_nsmul_poles_of_constantCompositum_eq_top`), and every divisor of `F'` is
linearly equivalent to one below some `l B`.

When `k' / k` is finite the conorm `Con : Div(F) → Div(F')` is defined; it preserves degrees and
the dimensions of Riemann–Roch spaces, so it carries the canonical class to the canonical class
and is injective on divisor classes.

Exactness of `k'` in `F'` is not needed for the degree and genus identities; where the canonical
class of `F' / k'` is spoken of, it follows from exactness of `k` in `F`
(`IsIntegrallyClosedIn.of_constantCompositum_eq_top`).

The genus never increases under any algebraic extension of constants, including inseparable
and infinite extensions. For a finite extension the conorm comparison also gives
`[k' : k] (g(F' / k') - 1) ≤ [F' : F] (g(F / k) - 1)`. Without separability the genus inequality
can be strict (`TauCeti.GenusDrop.genus_lt_genus`).

## Main results

* `TauCeti.finrank_mul_genus_sub_one_le_of_constantCompositum_eq_top`:
  `[k' : k] (g(F' / k') - 1) ≤ [F' : F] (g(F / k) - 1)` for any finite `k' / k`.
* `TauCeti.genus_le_genus_of_constantCompositum_eq_top`: `g(F' / k') ≤ g(F / k)` for any
  algebraic `k' / k`, finite or not, separable or not.
* `TauCeti.Divisor.degree_conorm_of_constantCompositum_eq_top`: `deg (Con D) = deg D`.
* `TauCeti.genus_eq_genus_of_constantCompositum_eq_top`: `g(F' / k') = g(F / k)` for a separable
  algebraic `k' / k`, finite or not.
* `TauCeti.conormClassGroup_canonicalClass_of_constantCompositum_eq_top`: the conorm of the
  canonical class is the canonical class.
* `TauCeti.conormClassGroup_injective_of_constantCompositum_eq_top`: the conorm is injective on
  divisor classes.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, second edition, Section III.6,
  Theorem 3.6.3(b), (c), (e) and (f).
* J. Tate, *Genus change in inseparable extensions of function fields*, Proc. Amer. Math. Soc. 3
  (1952), 400–406, for the genus change under inseparable constant field extensions.
-/

public section

open scoped IntermediateField

namespace TauCeti

universe u u' v v'

variable {k : Type u} {k' : Type u'} {F : Type v} {F' : Type v'}
variable [Field k] [Field k'] [Field F] [Field F']
variable [Algebra k k'] [Algebra k F] [Algebra k F'] [Algebra k' F'] [Algebra F F']
variable [IsScalarTower k k' F'] [IsScalarTower k F F']

/-! ### The genus never increases -/

section Finite

variable [FiniteDimensional k k']

/-- **The genus cannot grow under a finite constant field extension**, in quantitative form: if
`F' = F · k'` for a finite extension `k' / k`, then

`[k' : k] (g(F' / k') - 1) ≤ [F' : F] (g(F / k) - 1)`.

No separability of `k' / k` is assumed, nor exactness of `k` in `F` or of `k'` in `F'`.  Since
`[F' : F] ≤ [k' : k]`, this gives `g(F' / k') ≤ g(F / k)`
(`TauCeti.genus_le_genus_of_constantCompositum_eq_top`).  For a separable `k' / k` over an exact
constant field the two degrees agree and the genus is unchanged
(`TauCeti.genus_eq_genus_of_constantCompositum_eq_top`); an inseparable `k' / k` can make it drop
(`TauCeti.GenusDrop.genus_lt_genus`). -/
theorem finrank_mul_genus_sub_one_le_of_constantCompositum_eq_top (hF : IsFunctionField k F)
    (h : constantCompositum F k' F' = ⊤) :
    (Module.finrank k k' : ℤ) * (genus k' F' - 1) ≤ Module.finrank F F' * (genus k F - 1) := by
  have := finiteDimensional_of_constantCompositum_eq_top (k := k) h
  have hF' : IsFunctionField k' F' := hF.of_constantCompositum_eq_top h
  have hn : (Module.finrank F F' : ℤ) ≤ Module.finrank k k' := by
    exact_mod_cast finrank_le_finrank_of_constantCompositum_eq_top h
  have hn0 : (0 : ℤ) ≤ Module.finrank F F' := by positivity
  -- every divisor `D'` of `F' / k'` lies below a conorm `Con D`, which `F / k` controls
  have key (D' : Divisor k' F') :
      (Module.finrank k k' : ℤ) * (Divisor.degree D' + 1 - D'.dim) ≤
        Module.finrank F F' * (genus k F - 1) + Module.finrank k k' := by
    obtain ⟨D, hD⟩ := Divisor.exists_le_conorm (k := k) (F := F) k' F' D'
    have hcomp := mul_le_mul_of_nonneg_left (Divisor.dim_le_dim_add_degree_sub hF' hD)
      (Nat.cast_nonneg (α := ℤ) (Module.finrank k k'))
    have hdeg := Divisor.finrank_mul_degree_conorm k' F' hF D
    have hdim : (Module.finrank F F' : ℤ) * D.dim ≤
        Module.finrank k k' * (Divisor.conorm k' F' D).dim := by
      exact_mod_cast Divisor.finrank_mul_dim_le_finrank_mul_dim_conorm hF h D
    have hR := mul_le_mul_of_nonneg_left (Divisor.degree_add_one_sub_dim_le_genus hF D) hn0
    linarith
  rcases Nat.eq_zero_or_pos (genus k' F') with hg | hg
  · have := mul_nonneg hn0 (Nat.cast_nonneg (α := ℤ) (genus k F))
    rw [hg, Nat.cast_zero]
    linarith
  · obtain ⟨D', hD'⟩ := exists_degree_add_one_sub_dim_eq_genus_of_pos hF' hg
    have := key D'
    rw [hD'] at this
    linarith

/-- The finite case of `TauCeti.genus_le_genus_of_constantCompositum_eq_top`, read off the
quantitative inequality `TauCeti.finrank_mul_genus_sub_one_le_of_constantCompositum_eq_top`. -/
private theorem genus_le_genus_of_finiteDimensional (hF : IsFunctionField k F)
    (h : constantCompositum F k' F' = ⊤) : genus k' F' ≤ genus k F := by
  have := finiteDimensional_of_constantCompositum_eq_top (k := k) h
  have hmul := finrank_mul_genus_sub_one_le_of_constantCompositum_eq_top hF h
  have hn : (Module.finrank F F' : ℤ) ≤ Module.finrank k k' := by
    exact_mod_cast finrank_le_finrank_of_constantCompositum_eq_top h
  have hn0 : (0 : ℤ) < Module.finrank F F' := by exact_mod_cast Module.finrank_pos
  by_contra hlt
  replace hlt : (genus k F : ℤ) + 1 ≤ genus k' F' := by omega
  -- then `[k' : k] (g' - 1) ≥ [k' : k] g ≥ [F' : F] g > [F' : F] (g - 1)`
  have h₁ := mul_le_mul_of_nonneg_left (sub_le_sub_right hlt 1) (hn0.le.trans hn)
  have h₂ := mul_le_mul_of_nonneg_right hn (Nat.cast_nonneg (α := ℤ) (genus k F))
  linarith

end Finite

section IsAlgebraic

/-- A linearly disjoint algebraic extension of constants cannot increase the genus.
The pole-divisor degrees do not increase, while the Riemann–Roch dimensions do not decrease. -/
private theorem genus_le_genus_of_linearDisjoint [Algebra.IsAlgebraic k k']
    (hF : IsFunctionField k F) (h : constantCompositum F k' F' = ⊤)
    (H : (IsScalarTower.toAlgHom k k' F').fieldRange.LinearDisjoint F) :
    genus k' F' ≤ genus k F := by
  have hF' : IsFunctionField k' F' := hF.of_constantCompositum_eq_top h
  have := isAlgebraic_of_constantCompositum_eq_top (k := k) h
  -- the pole divisor `B` of a transcendental `x` and its counterpart `B'` in `F'`
  obtain ⟨x, hx⟩ := hF.exists_transcendental
  have := hF.finiteDimensional_adjoin hx
  set z := Units.mk0 x hx.ne_zero
  set B := Divisor.poles hF z
  set B' := Divisor.poles hF' (Units.map (algebraMap F F' : F →* F') z)
  have hx' : Transcendental k' (algebraMap F F' x) := hx.algebraMap_of_isAlgebraic
  have := hF'.finiteDimensional_adjoin hx'
  have hdegB' : Divisor.degree B' = Module.finrank k'⟮algebraMap F F' x⟯ F' :=
    Divisor.degree_poles hF' _ (by simpa [z, Transcendental] using hx')
  have hdeg : Divisor.degree B' ≤ Divisor.degree B := by
    rw [Divisor.degree_poles hF z hx, hdegB']
    exact_mod_cast finrank_over_adjoin_simple_le_of_constantCompositum_eq_top h x
  have hpos : 0 < Divisor.degree B' := by
    rw [hdegB']
    exact_mod_cast Module.finrank_pos
  refine genus_le fun D' ↦ ?_
  -- `L(l B' - D')` is nonzero for large `l`, so `deg D' + 1 - ℓ(D')` is at most the value at
  -- `l B'`, which is at most the value at `l B`
  obtain ⟨l, hl⟩ : ∃ l : ℕ, Divisor.degree D' + genus k' F' ≤ l * Divisor.degree B' :=
    ⟨(Divisor.degree D' + genus k' F').toNat,
      by nlinarith [Int.self_le_toNat (Divisor.degree D' + genus k' F')]⟩
  have hne : riemannRochSpace (l • B' - D') ≠ ⊥ := by
    refine (Divisor.one_le_dim_iff_riemannRochSpace_ne_bot hF' _).1 ?_
    have := Divisor.degree_add_one_sub_genus_le_dim hF' (l • B' - D')
    rw [Divisor.degree_sub, map_nsmul, nsmul_eq_mul] at this
    omega
  have hcomp := Divisor.dim_sub_degree_le_of_riemannRochSpace_ne_bot hF' hne
  have hR := Divisor.degree_add_one_sub_dim_le_genus hF (l • B)
  rw [map_nsmul, nsmul_eq_mul] at hcomp hR
  have hdim : (l • B).dim ≤ (l • B').dim :=
    Divisor.dim_nsmul_poles_le_of_linearDisjoint hF hF' H l z
  have : (l : ℤ) * Divisor.degree B' ≤ l * Divisor.degree B :=
    mul_le_mul_of_nonneg_left hdeg (Nat.cast_nonneg l)
  omega

/-- For a function field `E / K` of degree `n` over a rational subfield, every algebraic
extension of its constants has genus at most that of `E / K`. -/
private theorem genus_le_genus_aux (n : ℕ) :
    ∀ (K : Type u') (E : Type v') [Field K] [Field E] [Algebra K k'] [Algebra K E]
      [Algebra K F'] [Algebra E F'] [IsScalarTower K k' F'] [IsScalarTower K E F']
      [Algebra.IsAlgebraic K k'], IsFunctionField K E → constantCompositum E k' F' = ⊤ →
      ∀ x : E, Transcendental K x → Module.finrank K⟮x⟯ E = n → genus k' F' ≤ genus K E := by
  -- Induct on the degree over a rational subfield. A finite constant extension either
  -- preserves the degree or reduces it, yielding a smaller-degree comparison.
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro K E _ _ _ _ _ _ _ _ _ hE h x hx hn
  by_cases hdisj : ∀ M : IntermediateField K k', FiniteDimensional K M →
      Module.finrank E (constantCompositum E M F') = Module.finrank K M
  · exact genus_le_genus_of_linearDisjoint hE h
      (linearDisjoint_fieldRange_of_forall_finrank_constantCompositum_eq hdisj)
  push Not at hdisj
  obtain ⟨M, _, hM⟩ := hdisj
  -- the lower field `E · M`, a function field over `M`
  let EM := constantCompositum E M F'
  let := constantCompositumAlgebra E M F'
  have := isScalarTower_constantCompositum E M F'
  have := isScalarTower_base_constantCompositum K E M F'
  have hEM : constantCompositum E M EM = ⊤ := (constantCompositum_eq_top_iff E M F' EM).2 rfl
  have := finiteDimensional_of_constantCompositum_eq_top (k := K) hEM
  have hFEM : IsFunctionField M EM := hE.of_constantCompositum_eq_top hEM
  have : Algebra.IsAlgebraic M k' := .tower_top (K := K) M
  set z := Units.mk0 x hx.ne_zero
  have hx' : Transcendental M (algebraMap E EM x) := hx.algebraMap_of_isAlgebraic
  -- `[M : K] · [E · M : M(x)] = [E · M : E] · n`, and `[E · M : E] < [M : K]`
  have hlt : Module.finrank M⟮algebraMap E EM x⟯ EM < n := by
    have hconorm := Divisor.finrank_mul_degree_conorm M EM hE (Divisor.poles hE z)
    rw [Divisor.conorm_poles M EM hE hFEM, Divisor.degree_poles hFEM _
      (by simpa [z, Transcendental] using hx'), Divisor.degree_poles hE z hx] at hconorm
    simp only [Units.coe_map, MonoidHom.coe_ofClass, Units.val_mk0, z] at hconorm
    have hconorm' : Module.finrank K M * Module.finrank M⟮algebraMap E EM x⟯ EM =
        Module.finrank E EM * Module.finrank K⟮x⟯ E := by
      exact_mod_cast hconorm
    have hle : Module.finrank E EM < Module.finrank K M :=
      lt_of_le_of_ne (finrank_le_finrank_of_constantCompositum_eq_top hEM) hM
    have := hE.finiteDimensional_adjoin hx
    have hpos : 0 < Module.finrank K⟮x⟯ E := Module.finrank_pos
    rw [← hn]
    by_contra hcon
    push Not at hcon
    have := Nat.mul_le_mul_left (Module.finrank K M) hcon
    have := Nat.mul_lt_mul_of_pos_right hle hpos
    omega
  calc genus k' F'
      ≤ genus M EM := ih _ hlt M EM hFEM (constantCompositum_eq_top_of_eq_top E k' F' EM h) _ hx'
        rfl
    _ ≤ genus K E := genus_le_genus_of_finiteDimensional hE hEM

/-- **The genus never increases under an algebraic constant field extension**: if `F' = F · k'`
for an algebraic extension `k' / k`, finite or not, then `g(F' / k') ≤ g(F / k)`.  No separability
or exactness hypothesis is needed.  The inequality is strict for some inseparable extensions
(`TauCeti.GenusDrop.genus_lt_genus`), and an equality for separable ones over an exact constant
field (`TauCeti.genus_eq_genus_of_constantCompositum_eq_top`).  For an algebraic closure `k'` of
`k`, it bounds the genus of `F · k' / k'` by that of `F / k`. -/
theorem genus_le_genus_of_constantCompositum_eq_top [Algebra.IsAlgebraic k k']
    (hF : IsFunctionField k F) (h : constantCompositum F k' F' = ⊤) : genus k' F' ≤ genus k F := by
  -- pass to the copy `F · ⊥` of `F` inside `F'`, whose constants live in the universe of `k'`
  let M : IntermediateField k k' := ⊥
  let E := constantCompositum F M F'
  let := constantCompositumAlgebra F M F'
  have := isScalarTower_constantCompositum F M F'
  have := isScalarTower_base_constantCompositum k F M F'
  have hE : constantCompositum F M E = ⊤ := (constantCompositum_eq_top_iff F M F' E).2 rfl
  have hFE : IsFunctionField M E := hF.of_constantCompositum_eq_top hE
  have : Algebra.IsAlgebraic M k' := .tower_top (K := k) M
  obtain ⟨x, hx⟩ := hF.exists_transcendental
  have hx' : Transcendental M (algebraMap F E x) := hx.algebraMap_of_isAlgebraic
  calc genus k' F'
      ≤ genus M E :=
        genus_le_genus_aux _ M E hFE (constantCompositum_eq_top_of_eq_top F k' F' E h) _ hx' rfl
    _ ≤ genus k F := genus_le_genus_of_finiteDimensional hF hE

end IsAlgebraic

/-! ### The genus under separable algebraic constant field extensions -/

section Algebraic

variable [Algebra.IsSeparable k k']

/-- **The genus is unchanged by a separable algebraic constant field extension** (Stichtenoth,
Theorem 3.6.3(b)): if `k` is the exact constant field of `F` and `F' = F · k'` for a separable
algebraic extension `k' / k`, finite or not, then `g(F' / k') = g(F / k)`.  Exactness of `k'` in
`F'` is not assumed.  Over a perfect `k` this applies to an algebraic closure of `k`. -/
theorem genus_eq_genus_of_constantCompositum_eq_top (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) (h : constantCompositum F k' F' = ⊤) :
    genus k' F' = genus k F := by
  have hF' : IsFunctionField k' F' := hF.of_constantCompositum_eq_top h
  -- the pole divisor `B` of a transcendental `x` and its counterpart `B'` in `F'`
  obtain ⟨x, hx⟩ := hF.exists_transcendental
  set z := Units.mk0 x hx.ne_zero
  set B := Divisor.poles hF z
  set B' := Divisor.poles hF' (Units.map (algebraMap F F' : F →* F') z)
  have hx' : Transcendental k' (algebraMap F F' x) := hx.algebraMap_of_isAlgebraic
  have hdegB : Divisor.degree B = Module.finrank k⟮x⟯ F := Divisor.degree_poles hF z hx
  have hdeg : Divisor.degree B' = Divisor.degree B := by
    rw [hdegB, ← finrank_over_adjoin_simple_eq_of_constantCompositum_eq_top hex h x]
    exact Divisor.degree_poles hF' _ (by simpa [z, Transcendental] using hx')
  have hpos : 0 < Divisor.degree B := by
    have := hF.finiteDimensional_adjoin hx
    rw [hdegB]
    exact_mod_cast Module.finrank_pos
  have hdim (l : ℕ) : (l • B').dim = (l • B).dim :=
    Divisor.dim_nsmul_poles_of_constantCompositum_eq_top hF hex h l z
  -- the genus never increases; in large degree `l B` attains the genus of `F`, and `l B'` has
  -- the same degree and dimension
  refine le_antisymm (genus_le_genus_of_constantCompositum_eq_top hF h) ?_
  obtain ⟨c, hc⟩ := exists_forall_dim_eq_degree_add_one_sub_genus hF hex
  obtain ⟨l, hl⟩ : ∃ l : ℕ, c ≤ l * Divisor.degree B :=
    ⟨c.toNat, by nlinarith [Int.self_le_toNat c]⟩
  have hgen := hc (l • B) (by rwa [map_nsmul, nsmul_eq_mul])
  have hR := Divisor.degree_add_one_sub_dim_le_genus hF' (l • B')
  rw [map_nsmul, hdeg, hdim, ← map_nsmul] at hR
  exact_mod_cast (by linarith : (genus k F : ℤ) ≤ genus k' F')

end Algebraic

/-! ### Finite separable constant field extensions -/

variable [FiniteDimensional F F'] [Algebra.IsSeparable k k']

/-- **The conorm along a constant field extension preserves degrees** (Stichtenoth,
Theorem 3.6.3(c)): for a finite separable constant field extension `F · k' / k'` of `F / k` with
exact constant field `k`, `deg (Con D) = deg D` for every divisor `D` of `F / k`.  No
function-field hypothesis on `F / k` is needed. -/
@[simp]
theorem Divisor.degree_conorm_of_constantCompositum_eq_top
    (hex : IsIntegrallyClosedIn k F) (h : constantCompositum F k' F' = ⊤) (D : Divisor k F) :
    Divisor.degree (Divisor.conorm k' F' D) = Divisor.degree D := by
  have := finiteDimensional_base_of_constantCompositum_eq_top hex h
  have := isSeparable_of_constantCompositum_eq_top (k := k) (k' := k') h
  rw [Divisor.degree_conorm_of_isSeparable k' F'
    (finrank_constantCompositum_eq_finrank_of_isSeparable F k' F' hex),
    geometricDegree_eq_one_of_constantCompositum_eq_top F k' F' h, Nat.cast_one, one_mul]

/-- **The conorm of the canonical class is the canonical class** (Stichtenoth,
Theorem 3.6.3(e)): for a finite separable constant field extension `F · k' / k'` of `F / k` with
exact constant field `k`, the conorm on divisor classes sends the canonical class of `F / k` to the
canonical class of `F · k' / k'`, whose constant field `k'` is exact as well. -/
@[simp]
theorem conormClassGroup_canonicalClass_of_constantCompositum_eq_top (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) (h : constantCompositum F k' F' = ⊤) :
    Divisor.conormClassGroup k' F' hF (hF.of_constantCompositum_eq_top h) (canonicalClass hF hex) =
      canonicalClass (hF.of_constantCompositum_eq_top h)
        (hex.of_constantCompositum_eq_top h) := by
  have hF' : IsFunctionField k' F' := hF.of_constantCompositum_eq_top h
  have hex' := hex.of_constantCompositum_eq_top h
  obtain ⟨W, hW⟩ := (Place.orderSystem hF).divisorClass_surjective (canonicalClass hF hex)
  have hW' := (divisorClass_eq_canonicalClass_iff hF hex W).1 hW
  rw [← hW, Divisor.conormClassGroup_divisorClass, divisorClass_eq_canonicalClass_iff hF' hex',
    Divisor.dim_conorm hex h hF, Divisor.degree_conorm_of_constantCompositum_eq_top hex h,
    genus_eq_genus_of_constantCompositum_eq_top hF hex h]
  exact hW'

/-- **The conorm is injective on divisor classes** (Stichtenoth, Theorem 3.6.3(f)): along a finite
separable constant field extension of a function field with exact constant field, two divisors
with the same conorm class lie in the same class; equivalently, a divisor whose conorm is principal
is itself principal. -/
theorem conormClassGroup_injective_of_constantCompositum_eq_top (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) (h : constantCompositum F k' F' = ⊤) :
    Function.Injective (Divisor.conormClassGroup k' F' hF (hF.of_constantCompositum_eq_top h)) := by
  have hF' : IsFunctionField k' F' := hF.of_constantCompositum_eq_top h
  rw [injective_iff_map_eq_zero]
  intro c hc
  obtain ⟨D, rfl⟩ := (Place.orderSystem hF).divisorClass_surjective c
  rw [Divisor.conormClassGroup_divisorClass, Divisor.divisorClass_eq_zero_iff hF'] at hc
  obtain ⟨z, hz⟩ := hc
  have hdeg : Divisor.degree D = 0 := by
    rw [← Divisor.degree_conorm_of_constantCompositum_eq_top hex h, ← hz,
      Divisor.degree_principal]
  have hdim : 1 ≤ Divisor.dim D := by
    rw [← Divisor.dim_conorm hex h hF]
    exact (Divisor.one_le_dim_iff_exists_principal_eq_of_degree_eq_zero hF' (by
      rw [Divisor.degree_conorm_of_constantCompositum_eq_top hex h, hdeg])).2 ⟨z, hz⟩
  exact (Divisor.divisorClass_eq_zero_iff hF).2
    ((Divisor.one_le_dim_iff_exists_principal_eq_of_degree_eq_zero hF hdeg).1 hdim)

end TauCeti
