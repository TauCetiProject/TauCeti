/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Consequences.Clifford
public import TauCeti.FieldTheory.FunctionField.ConstantExtension.Genus
public import TauCeti.FieldTheory.FunctionField.Frobenius
public import TauCeti.FieldTheory.IntermediateField.LinearDisjoint
public import TauCeti.LinearAlgebra.LinearIndependent.Frobenius

/-!
# Separating elements in Riemann–Roch spaces of small degree

Let `F / k` be an algebraic function field of exponential characteristic `p`. A Riemann–Roch
space `L(D)` of small degree cannot consist of `p`-th powers alone once its dimension is large
compared with `deg D / p`. Taking `p`-th roots is injective, additive and semilinear for the
Frobenius of `k`, and the `p`-th root of a function whose poles are bounded by `D` has poles
bounded by `⌊D / p⌋`. So a `k`-subspace `V ⊆ L(D)` of `p`-th powers has dimension at most
`ℓ(⌊D / p⌋)`, and Clifford's theorem bounds this by `deg D / (2p) + 1`.

Over a perfect field the elements outside `F^p` are exactly the separating elements. For a
function field of genus `g ≥ 2` with exact constant field, applied to the Riemann–Roch space
`L(W)` of an effective canonical divisor, of dimension `g` and degree `2g - 2`, this produces a
separating element `x` with `[F : k(x)] ≤ 2g - 2`, exhibiting `F` as a separable cover of the
projective line of degree at most `2g - 2`.

The bound on `p`-th powers needs no hypothesis on `k`, and it holds equally after a constant
field extension `F' = F · k'` with `F` and `k'` linearly disjoint over `k`: if a `k`-basis of
`L(D)` consists of `p`-th powers in `F'`, their `p`-th roots are linearly independent over `k'`
and have poles bounded by `⌊Con D / p⌋`, against Clifford's theorem in `F' / k'`. For an infinite
algebraic `k' / k` the roots are defined over a finite subextension. Over an imperfect field `k`
the elements outside `F^p` need not be separating, and this is how the bound is used: if `k'` is
perfect, exact in `F'`, and `F' / k'` keeps the genus of `F / k`, then a function of `F` with
vanishing differential becomes a `p`-th power in `F'`. So a function field of genus `g ≥ 2`
that is separably generated over `k` and has such an extension `k'` has a separating element of
degree at most `2g - 2`. A separating element `x` of small degree is what produces places of
small degree with separable residue field: those above the rational places of `k(x)` at which
`F / k(x)` is unramified.

## Main results

* `TauCeti.Divisor.finrank_le_dim_of_forall_mem_fieldRange_frobenius`: a subspace of `L(D)`
  consisting of `p`-th powers has dimension at most `ℓ(E)` whenever `D < p (E + 1)`.
* `TauCeti.Divisor.exists_algebraMap_notMem_fieldRange_frobenius_of_constantCompositum_eq_top`:
  after a finite linearly disjoint constant field extension `F · k'` with exact constants and
  genus `g'`, a `k`-independent family in `L(D)` with `0 ≤ deg D ≤ 2g' - 2` and
  `deg D < p (2 #b - 2)` is not made of `p`-th powers.
* `TauCeti.Divisor.exists_algebraMap_notMem_fieldRange_frobenius_of_linearDisjoint`: the same
  for an algebraic, possibly infinite, linearly disjoint constant field extension.
* `TauCeti.Divisor.exists_mem_notMem_fieldRange_frobenius`: if `0 ≤ deg D ≤ 2g - 2` and
  `deg D < p (2 dim V - 2)`, then a subspace `V ⊆ L(D)` contains an element which is not a
  `p`-th power.
* `TauCeti.Divisor.exists_mem_transcendental_and_isSeparable_adjoin`: over a perfect field, such
  a `V` contains a separating element.
* `TauCeti.IsFunctionField.exists_transcendental_and_isSeparable_adjoin_and_finrank_le`: over a
  perfect field, a function field of genus `g ≥ 2` with exact constant field has a separating
  element `x` with `[F : k(x)] ≤ 2g - 2`.
* `exists_transcendental_and_isSeparable_adjoin_and_finrank_le_of_constantCompositum_eq_top`,
  in the namespace `TauCeti.IsFunctionField`: over an arbitrary field, the separating element
  of degree at most `2g - 2`, given a perfect constant field extension that keeps the constants
  exact and the genus.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Theorem 1.6.13 (Clifford's theorem) and Proposition 3.10.2 (separating elements).
* The Stacks Project, Section 55.18, [Tag 0CDL](https://stacks.math.columbia.edu/tag/0CDL),
  Theorem [0CDM](https://stacks.math.columbia.edu/tag/0CDM), whose degree bound uses a point of
  the curve over a separable extension of degree at most `2g - 2`; the separating element above
  is the function field input to that point.
-/

public section

open Module

open scoped IntermediateField

namespace TauCeti

open AlgebraicGeometry

variable {k F : Type*} [Field k] [Field F] [Algebra k F]

namespace Divisor

/-- **Riemann–Roch spaces of `p`-th powers.** A `k`-subspace `V ⊆ L(D)` consisting of `p`-th
powers has dimension at most `ℓ(E)` for every divisor `E` with `D < p (E + 1)`, for instance
`E = ⌊D / p⌋`. No hypothesis on the constant field `k` is needed. -/
theorem finrank_le_dim_of_forall_mem_fieldRange_frobenius (hF : IsFunctionField k F) (p : ℕ)
    [ExpChar F p] {D E : Divisor k F} (hDE : ∀ P : Place k F, D.coeff P < p * (E.coeff P + 1))
    {V : Submodule k F} (hV : V ≤ riemannRochSpace D)
    (hVp : ∀ v ∈ V, v ∈ (frobenius F p).fieldRange) :
    finrank k V ≤ dim E := by
  -- Taking `p`-th roots embeds `V` into `L(E)`, semilinearly for the Frobenius of `k`.
  let _ : ExpChar k p := (algebraMap k F).expChar (algebraMap k F).injective p
  have : FiniteDimensional k (riemannRochSpace E) := finiteDimensional_riemannRochSpace hF E
  -- The `p`-th root of an element of `V`.
  let root : V → F := fun v ↦ (frobenius F p).rangeRestrictFieldEquiv.symm ⟨v, hVp v v.2⟩
  have hroot (v : V) : root v ^ p = v := by
    have h := (frobenius F p).rangeRestrictFieldEquiv_apply_symm_apply ⟨v, hVp v v.2⟩
    rwa [frobenius_def] at h
  have hrootE (v : V) : root v ∈ riemannRochSpace E :=
    mem_riemannRochSpace_of_pow_mem (expChar_pos F p) hDE (by rw [hroot v]; exact hV v.2)
  -- Taking `p`-th roots is additive and injective.
  let j : V →+ riemannRochSpace E :=
    { toFun v := ⟨root v, hrootE v⟩
      map_zero' := by
        ext
        refine (frobenius_inj F p) ?_
        rw [ZeroMemClass.coe_zero, map_zero, frobenius_def]
        exact hroot 0
      map_add' a b := by
        ext
        refine (frobenius_inj F p) ?_
        simp only [frobenius_def, Submodule.coe_add, add_pow_expChar, hroot] }
  have hj : Function.Injective j := fun a b hab ↦ by
    have h := congrArg (fun y : riemannRochSpace E ↦ (y : F) ^ p) hab
    simp only [j, AddMonoidHom.coe_mk, ZeroHom.coe_mk, hroot] at h
    exact Subtype.ext h
  have hc (r : k) (v : V) : j (frobenius k p r • v) = r • j v := by
    ext
    refine (frobenius_inj F p) ?_
    simp only [j, AddMonoidHom.coe_mk, ZeroHom.coe_mk, frobenius_def, SetLike.val_smul, hroot,
      Algebra.smul_def, mul_pow, map_pow]
  rw [dim_def]
  exact finrank_le_finrank_of_rank_le_rank
    (lift_rank_le_of_injective_injectiveₛ (frobenius k p) j (frobenius_inj k p) hj hc)
    (Module.rank_lt_aleph0 k _)

/-! ### Riemann–Roch spaces after a constant field extension

The `p`-th roots in a constant field extension `F' = F · k'` of a `k`-basis of `L(D)` are linearly
independent over `k'` as soon as `F` and `k'` are linearly disjoint over `k`, and their poles are
bounded by `⌊Con D / p⌋`. So Clifford's theorem in `F' / k'` bounds the number of basis elements
that can become `p`-th powers in `F'`. The case `k' = k` is the bound for `F` itself. For an
infinite algebraic `k' / k` the roots lie over a finite subextension `M`, where the genus of
`F · M / M` is at least that of `F' / k'`.
-/

section ConstantExtension

variable {k' F' : Type*} [Field k'] [Field F'] [Algebra k k'] [Algebra k F'] [Algebra k' F']
  [Algebra F F'] [IsScalarTower k k' F'] [IsScalarTower k F F']

/-- **A Riemann–Roch space of small degree is not made of `p`-th powers after a constant field
extension.** Let `F' = F · k'` for a finite extension `k' / k` with `[F' : F] = [k' : k]`, and let
`k'` be the exact constant field of `F'`, of genus `g'`. If `D` is a divisor of `F / k` with
`0 ≤ deg D ≤ 2g' - 2` and `b` is a `k`-linearly independent family in `L(D)` with
`deg D < p (2 #b - 2)`, then some `b i` is not a `p`-th power in `F'`. Neither `k` nor `k'` need
be perfect, and `k' / k` need not be separable. -/
theorem exists_algebraMap_notMem_fieldRange_frobenius_of_constantCompositum_eq_top
    [FiniteDimensional k k'] (hF : IsFunctionField k F) (h : constantCompositum F k' F' = ⊤)
    (hdisj : finrank F (constantCompositum F k' F') = finrank k k')
    (hex' : IsIntegrallyClosedIn k' F') (p : ℕ) [ExpChar F' p] {D : Divisor k F}
    (hD₀ : 0 ≤ degree D) (hDg : degree D ≤ 2 * (genus k' F' : ℤ) - 2) {ι : Type*} [Fintype ι]
    {b : ι → F} (hbD : ∀ i, b i ∈ riemannRochSpace D) (hb : LinearIndependent k b)
    (hlt : degree D < p * (2 * (Fintype.card ι : ℤ) - 2)) :
    ∃ i, algebraMap F F' (b i) ∉ (frobenius F' p).fieldRange := by
  by_contra! hbp
  have := finiteDimensional_of_constantCompositum_eq_top (k := k) h
  have hF' : IsFunctionField k' F' := hF.of_constantCompositum_eq_top h
  have hp : 0 < (p : ℤ) := by exact_mod_cast expChar_pos F' p
  -- The conorm `Con D` has the degree of `D`.
  have hdegCon : degree (conorm k' F' D) = degree D := by
    rw [degree_conorm k' F' hF hdisj D, (geometricDegree_eq_one_iff F k' F').2 h, Nat.cast_one,
      one_mul]
  -- The divisor `E = ⌊Con D / p⌋` of `F' / k'`.
  let E : Divisor k' F' := Finsupp.mapRange (· / (p : ℤ)) (Int.zero_ediv _) (conorm k' F' D)
  have hE (P : Place k' F') : E.coeff P = (conorm k' F' D).coeff P / p :=
    Finsupp.mapRange_apply ..
  -- The `p`-th roots `β i` of the `b i` lie in `L(E)`.
  choose β hβ using hbp
  have hβ' (i : ι) : β i ^ p = algebraMap F F' (b i) := by
    rw [← frobenius_def]
    exact hβ i
  have hβE (i : ι) : β i ∈ riemannRochSpace E := by
    refine mem_riemannRochSpace_of_pow_mem (D := conorm k' F' D) (expChar_pos F' p)
      (fun P ↦ ?_) (by rw [hβ' i]; exact (mem_riemannRochSpace_conorm_iff hF' D (b i)).2 (hbD i))
    -- `Con D < p (⌊Con D / p⌋ + 1)`.
    rw [hE, mul_add_one]
    exact Int.lt_mul_ediv_self_add hp
  -- The `β i` are linearly independent over `k'`, since their `p`-th powers `b i` stay
  -- independent over `k'` by linear disjointness.
  have hβli : LinearIndependent k' β := by
    have hd := linearDisjoint_fieldRange_of_finrank_constantCompositum_eq hdisj
    refine .of_pow_expChar_pow p 1 ?_
    simpa only [pow_one, hβ', Function.comp_def] using hd.linearIndependent_algebraMap_comp hb
  -- So `#ι ≤ ℓ(E)`.
  have : FiniteDimensional k' (riemannRochSpace E) := finiteDimensional_riemannRochSpace hF' E
  have hdim : Fintype.card ι ≤ dim E := by
    rw [dim_def]
    exact (LinearIndependent.of_comp (riemannRochSpace E).subtype
      (v := fun i ↦ (⟨β i, hβE i⟩ : riemannRochSpace E)) hβli).fintype_card_le_finrank
  -- `p • E ≤ Con D`, so `p deg E ≤ deg D`.
  have hpE : (p : ℤ) • E ≤ conorm k' F' D := WeilDivisor.le_iff.mpr fun P ↦ by
    rw [WeilDivisor.coeff_zsmul, hE]
    exact Int.mul_ediv_self_le hp.ne'
  have hdegE : (p : ℤ) * degree E ≤ degree D := by
    simpa [hdegCon] using degree_le_of_le hpE
  rcases lt_or_ge (degree E) 0 with hneg | hnonneg
  · -- `L(E) = 0`, so `ι` is empty, against `0 ≤ deg D`.
    rw [dim_eq_zero_of_degree_neg hF' hneg] at hdim
    have hι : Fintype.card ι = 0 := by omega
    rw [hι] at hlt
    push_cast at hlt
    nlinarith
  · -- Clifford's theorem for `E`.
    have hcl := two_mul_dim_le_degree_add_two hF' hex' hnonneg (by nlinarith)
    have : 2 * (Fintype.card ι : ℤ) - 2 ≤ degree E := by
      have : (Fintype.card ι : ℤ) ≤ dim E := by exact_mod_cast hdim
      omega
    nlinarith

/-- **A Riemann–Roch space of small degree is not made of `p`-th powers after an algebraic
constant field extension.** Let `F' = F · k'` for an algebraic extension `k' / k`, finite or not,
such that `F` and `k'` are linearly disjoint over `k` and `k'` is the exact constant field of
`F'`, of genus `g'`. If `D` is a divisor of `F / k` with `0 ≤ deg D ≤ 2g' - 2` and `b` is a
`k`-linearly independent family in `L(D)` with `deg D < p (2 #b - 2)`, then some `b i` is not a
`p`-th power in `F'`. This extends
`exists_algebraMap_notMem_fieldRange_frobenius_of_constantCompositum_eq_top` to infinite
extensions such as a perfect closure of `k`. -/
theorem exists_algebraMap_notMem_fieldRange_frobenius_of_linearDisjoint
    [Algebra.IsAlgebraic k k'] (hF : IsFunctionField k F) (h : constantCompositum F k' F' = ⊤)
    (H : (IsScalarTower.toAlgHom k k' F').fieldRange.LinearDisjoint F)
    (hex' : IsIntegrallyClosedIn k' F') (p : ℕ) [ExpChar F' p] {D : Divisor k F}
    (hD₀ : 0 ≤ degree D) (hDg : degree D ≤ 2 * (genus k' F' : ℤ) - 2) {ι : Type*} [Fintype ι]
    {b : ι → F} (hbD : ∀ i, b i ∈ riemannRochSpace D) (hb : LinearIndependent k b)
    (hlt : degree D < p * (2 * (Fintype.card ι : ℤ) - 2)) :
    ∃ i, algebraMap F F' (b i) ∉ (frobenius F' p).fieldRange := by
  classical
  by_contra! hbp
  -- The `p`-th roots of the `b i` are defined over a finite subextension `M` of `k' / k`.
  choose β hβ using hbp
  obtain ⟨M, _, hβM⟩ :=
    exists_finiteDimensional_constantSubfield_of_finset_subset_constantCompositum (k := k)
      (F := F) (Finset.univ.image β) fun x _ ↦ h ▸ IntermediateField.mem_top
  have hdisjM := finrank_constantCompositum_eq_finrank_of_linearDisjoint F M F'
    (H.fieldRange_intermediateField M)
  let FM := constantCompositum F M F'
  let := constantCompositumAlgebra F M F'
  have := isScalarTower_constantCompositum F M F'
  have := isScalarTower_base_constantCompositum k F M F'
  have hFM : constantCompositum F M FM = ⊤ := (constantCompositum_eq_top_iff F M F' FM).2 rfl
  have hdisj : finrank F (constantCompositum F M FM) = finrank k M := by
    rw [hFM, IntermediateField.finrank_top']
    exact hdisjM
  -- The genus cannot increase on the way up from `F · M / M` to `F' / k'`.
  have : Algebra.IsAlgebraic M k' := .tower_top (K := k) M
  have hgM : genus k' F' ≤ genus M FM := genus_le_genus_of_constantCompositum_eq_top
    (hF.of_constantCompositum_eq_top hFM) (constantCompositum_eq_top_of_eq_top F k' F' FM h)
  have hDg' : degree D ≤ 2 * (genus M FM : ℤ) - 2 := by
    have : (genus k' F' : ℤ) ≤ genus M FM := by exact_mod_cast hgM
    omega
  have : ExpChar FM p := (algebraMap FM F').expChar (algebraMap FM F').injective p
  -- So the finite case applies to `F · M / M`, where the `β i` are `p`-th roots of the `b i`.
  obtain ⟨i, hi⟩ := exists_algebraMap_notMem_fieldRange_frobenius_of_constantCompositum_eq_top hF
    hFM hdisj (isIntegrallyClosedIn_constantCompositum_of_linearDisjoint H hex' M) p hD₀ hDg'
    hbD hb hlt
  exact hi ⟨⟨β i, hβM _ (Finset.mem_image_of_mem β (Finset.mem_univ i))⟩,
    Subtype.ext (by simpa [frobenius_def] using hβ i)⟩

end ConstantExtension

/-- **A Riemann–Roch space of small degree is not made of `p`-th powers.** Let `F / k` have exact
constant field and genus `g`, and let `D` be a divisor with `0 ≤ deg D ≤ 2g - 2`. A `k`-subspace
`V ⊆ L(D)` with `deg D < p (2 dim V - 2)` contains an element which is not a `p`-th power. No
hypothesis on `k` is needed. In characteristic zero, where `p = 1`, the hypotheses are
contradictory. This is the case `k' = k` of
`exists_algebraMap_notMem_fieldRange_frobenius_of_constantCompositum_eq_top`. -/
theorem exists_mem_notMem_fieldRange_frobenius (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) (p : ℕ) [ExpChar F p] {D : Divisor k F}
    (hD₀ : 0 ≤ degree D) (hDg : degree D ≤ 2 * (genus k F : ℤ) - 2) {V : Submodule k F}
    (hV : V ≤ riemannRochSpace D) (hlt : degree D < p * (2 * (finrank k V : ℤ) - 2)) :
    ∃ x ∈ V, x ∉ (frobenius F p).fieldRange := by
  -- This is the case `k' = k` of the constant field extension form, applied to a basis of `V`.
  by_contra! hVp
  have := finiteDimensional_riemannRochSpace hF D
  have : FiniteDimensional k V := Submodule.finiteDimensional_of_le hV
  let b := Module.finBasis k V
  obtain ⟨i, hi⟩ := exists_algebraMap_notMem_fieldRange_frobenius_of_constantCompositum_eq_top
    (k' := k) (F' := F) hF (Subsingleton.elim _ _) (by simp) hex p hD₀ hDg
    (b := fun i ↦ (b i : F)) (fun i ↦ hV (b i).2)
    (b.linearIndependent.map' V.subtype (Submodule.ker_subtype _)) (by simpa using hlt)
  exact hi (hVp _ (b i).2)

/-- **A separating element in a Riemann–Roch space of small degree.** Over a perfect field `k`,
let `F / k` have exact constant field and genus `g`, and let `D` be a divisor with
`0 ≤ deg D ≤ 2g - 2`. A `k`-subspace `V ⊆ L(D)` with `deg D < p (2 dim V - 2)` contains a
separating element: an `x` transcendental over `k` with `F / k(x)` separable. -/
theorem exists_mem_transcendental_and_isSeparable_adjoin [PerfectField k]
    (hF : IsFunctionField k F) (hex : IsIntegrallyClosedIn k F) (p : ℕ) [ExpChar F p]
    {D : Divisor k F} (hD₀ : 0 ≤ degree D) (hDg : degree D ≤ 2 * (genus k F : ℤ) - 2)
    {V : Submodule k F} (hV : V ≤ riemannRochSpace D)
    (hlt : degree D < p * (2 * (finrank k V : ℤ) - 2)) :
    ∃ x ∈ V, Transcendental k x ∧ Algebra.IsSeparable k⟮x⟯ F := by
  obtain ⟨x, hxV, hx⟩ := exists_mem_notMem_fieldRange_frobenius hF hex p hD₀ hDg hV hlt
  cases (inferInstance : ExpChar F p) with
  | zero => exact (hx ⟨x, by rw [frobenius_def, pow_one]⟩).elim
  | prime hp =>
    let _ : Fact p.Prime := ⟨hp⟩
    exact ⟨x, hxV, hF.transcendental_and_isSeparable_adjoin_of_notMem_fieldRange_frobenius p hx⟩

end Divisor

/-! ### Imperfect constant fields

Over an imperfect field the elements outside `F^p` need not be separating. Over a perfect
extension `k'` of `k`, a function of `F` with vanishing differential becomes a `p`-th power in
`F' = F · k'`. If `F' / k'` keeps the exact constants and the genus of `F / k`, the bound after a
constant field extension therefore gives an element of `L(W)` with nonzero differential, which is
separating when `F / k` is separably generated.
-/

section ConstantExtension

variable {k' F' : Type*} [Field k'] [Field F'] [Algebra k k'] [Algebra k F'] [Algebra k' F']
  [Algebra F F'] [IsScalarTower k k' F'] [IsScalarTower k F F']

namespace IsFunctionField

/-- **A separating element of degree at most `2g - 2` over an imperfect field.** Let `F / k` be a
function field of genus `g ≥ 2` with exact constant field and a separating element. Let
`F' = F · k'` for an algebraic extension `k' / k` with `k'` perfect, such that `F` and `k'` are
linearly disjoint over `k`, `k'` is the exact constant field of `F'` and `F' / k'` still has genus
`g`. Then `F` has a separating element `x` with `[F : k(x)] ≤ 2g - 2`. These hypotheses on `k'`
are the function field form of the smoothness and geometric integrality of a curve, with `k'` for
instance a perfect closure or an algebraic closure of `k`. -/
theorem exists_transcendental_and_isSeparable_adjoin_and_finrank_le_of_constantCompositum_eq_top
    [Algebra.IsAlgebraic k k'] [PerfectField k'] (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F)
    (hsep : ∃ z : F, Transcendental k z ∧ Algebra.IsSeparable k⟮z⟯ F)
    (h : constantCompositum F k' F' = ⊤)
    (H : (IsScalarTower.toAlgHom k k' F').fieldRange.LinearDisjoint F)
    (hex' : IsIntegrallyClosedIn k' F') (hgenus : genus k' F' = genus k F) (hg : 2 ≤ genus k F) :
    ∃ x : F, Transcendental k x ∧ Algebra.IsSeparable k⟮x⟯ F ∧
      finrank k⟮x⟯ F ≤ 2 * genus k F - 2 := by
  obtain ⟨W, hWeff, hW⟩ := exists_nonneg_isRiemannRochDivisor hF hex (by omega)
  have hdimW := hW.dim_eq hF hex
  have hdegW := hW.degree_eq hF hex
  -- It suffices to find a separating element of `L(W)`.
  suffices hx : ∃ x ∈ riemannRochSpace W, Transcendental k x ∧ Algebra.IsSeparable k⟮x⟯ F by
    obtain ⟨x, hxW, hxt, hxs⟩ := hx
    have hdeg := Divisor.finrank_adjoin_le_degree_of_mem_riemannRochSpace hF hWeff hxW hxt
    exact ⟨x, hxt, hxs, by omega⟩
  obtain ⟨p, hp⟩ := ExpChar.exists F
  cases hp with
  | zero =>
    -- In characteristic zero every transcendental `x ∈ L(W)` is separating.
    obtain ⟨x, hxW, hx⟩ :=
      Divisor.exists_mem_riemannRochSpace_transcendental hF hex (D := W) (by omega)
    have : FiniteDimensional k⟮x⟯ F := hF.finiteDimensional_adjoin hx
    exact ⟨x, hxW, hx, inferInstance⟩
  | prime hp =>
  have : Fact p.Prime := ⟨hp⟩
  have : ExpChar F' p := expChar_of_injective_algebraMap (algebraMap F F').injective p
  have : Algebra.EssFiniteType k F := hF.essFiniteType
  have : Algebra.Transcendental k F := trdeg_ne_zero_iff.mp (hF.trdeg_eq_one ▸ one_ne_zero)
  -- Since `F / k` is separably generated, an element with nonzero differential is separating.
  suffices hD : ∃ x ∈ riemannRochSpace W, KaehlerDifferential.D k F x ≠ 0 by
    obtain ⟨x, hxW, hx⟩ := hD
    exact ⟨x, hxW, transcendental_and_isSeparable_adjoin_of_D_ne_zero
      (finrank_kaehlerDifferential_eq_one_iff.2 hsep) hx⟩
  -- Over the perfect field `k'`, an element with vanishing differential is a `p`-th power in
  -- `F'`; but not every element of a basis of `L(W)` is one.
  have hF' : IsFunctionField k' F' := hF.of_constantCompositum_eq_top h
  have := finiteDimensional_riemannRochSpace hF W
  let b := Module.finBasis k (riemannRochSpace W)
  have hlt : Divisor.degree W <
      p * (2 * (Fintype.card (Fin (finrank k (riemannRochSpace W))) : ℤ) - 2) := by
    rw [Fintype.card_fin, ← Divisor.dim_def, hdimW, hdegW]
    have : (2 : ℤ) ≤ p := by exact_mod_cast hp.two_le
    have : (2 : ℤ) ≤ genus k F := by exact_mod_cast hg
    nlinarith
  obtain ⟨i, hi⟩ := Divisor.exists_algebraMap_notMem_fieldRange_frobenius_of_linearDisjoint hF h H
    hex' p (by omega) (by omega) (fun i ↦ (b i).2)
    (b.linearIndependent.map' (riemannRochSpace W).subtype (Submodule.ker_subtype _)) hlt
  refine ⟨b i, (b i).2, fun h0 ↦ hi ?_⟩
  rw [← hF'.D_eq_zero_iff_mem_fieldRange_frobenius p, ← KaehlerDifferential.map_D k k' F F', h0,
    map_zero]

/-- **A separating element of degree at most `2g - 2`.** Over a perfect field `k`, a function
field `F / k` of genus `g ≥ 2` with exact constant field has a separating element `x`, that is
transcendental over `k` with `F / k(x)` separable, of degree `[F : k(x)] ≤ 2g - 2`. For an
imperfect field see
`exists_transcendental_and_isSeparable_adjoin_and_finrank_le_of_constantCompositum_eq_top`. -/
theorem exists_transcendental_and_isSeparable_adjoin_and_finrank_le [PerfectField k]
    (hF : IsFunctionField k F) (hex : IsIntegrallyClosedIn k F) (hg : 2 ≤ genus k F) :
    ∃ x : F, Transcendental k x ∧ Algebra.IsSeparable k⟮x⟯ F ∧
      finrank k⟮x⟯ F ≤ 2 * genus k F - 2 :=
  -- This is the case `k' = k`, `F' = F` of the form over an imperfect field.
  exists_transcendental_and_isSeparable_adjoin_and_finrank_le_of_constantCompositum_eq_top
    (k' := k) (F' := F) hF hex hF.exists_transcendental_and_isSeparable_adjoin_of_perfectField
    (Subsingleton.elim _ _)
    ((IntermediateField.LinearDisjoint.bot_left k F F).of_le_left (by
      rintro _ ⟨c, rfl⟩
      exact IntermediateField.algebraMap_mem _ c))
    hex rfl hg

end IsFunctionField

end ConstantExtension

end TauCeti
