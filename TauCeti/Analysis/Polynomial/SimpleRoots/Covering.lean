/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Topology.Covering.Basic
public import TauCeti.Analysis.Polynomial.SimpleRoots.Basic
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import TauCeti.Analysis.Analytic.Inverse

/-!
# The roots of a family of separable polynomials form a covering space

Let `F : B → 𝕜[X]` be a family of polynomials of constant degree `d` over an algebraically closed
`RCLike` field (that is, over `ℂ`), whose coefficients depend continuously on the parameter `b`.
Its *root space* is the subtype `{q : B × 𝕜 // (F q.1).IsRoot q.2}` of pairs `(b, z)` with `z` a
root of `F b`, and it comes with the projection `(b, z) ↦ b`. Over the parameters at which `F b`
is separable, that is, at which its discriminant does not vanish, this projection is a covering
map whose fibres have `d` points. No continuous labelling of all the roots exists globally in
general, because of monodromy, but there is one near every separable member, and that local
labelling is the even covering.

When the parameter space is a normed space and the coefficients are analytic, the sheets of the
covering are analytic: a continuous function `r` with `r x` a root of `F x` is analytic at every
point where that root is simple. This is the analytic implicit root theorem applied to
`(x, z) ↦ (F x).eval z`, together with the uniqueness half of that theorem, which forces the
continuous root `r` to agree with the implicit root near the point.

These are the inputs for the Puiseux theorem with parameters: a monic polynomial with analytic
coefficients on `U × D`, whose discriminant vanishes only on `U × {0}`, has a root space which is a
`d`-sheeted covering of `U × (D \ {0})`. Lifting a power substitution through that covering gives
continuous root functions, and the analyticity statement here makes them analytic.

## Main results

* `TauCeti.Polynomial.analyticAt_eval_of_analyticAt_coeff`: a family with analytic coefficients
  and locally bounded degree is analytic in the parameter and the argument jointly.
* `TauCeti.Polynomial.analyticAt_of_eventually_isRoot`: **a continuous root of an analytic
  family is analytic** at a point where it is a simple root.
* `TauCeti.Polynomial.exists_continuousOn_isRoot_iff`: near a separable member of a continuous
  family of constant degree, the roots can be labelled by `d` continuous, pairwise distinct
  functions.
* `TauCeti.Polynomial.isEvenlyCovered_fst_isRoot`: the projection from the root space is evenly
  covered, with fibre `Fin d`, near every separable member.
* `TauCeti.Polynomial.isCoveringMapOn_fst_isRoot`,
  `TauCeti.Polynomial.isCoveringMap_fst_isRoot`: **the root space is a covering space** over the
  separable members, and over the whole parameter space when every member is separable.
* `TauCeti.Polynomial.preimageFstIsRootEquiv`: the fibre of the root space over `b` is the set of
  roots of `F b`.
* `TauCeti.Polynomial.finite_preimage_fst_isRoot`,
  `TauCeti.Polynomial.natCard_preimage_fst_isRoot`: the fibre over a separable member of degree
  `d` has exactly `d` points.

## References

* S. McCallum, A. Parusiński, L. Paunescu, *Validity proof of Lazard's method for CAD
  construction*, Journal of Symbolic Computation 92 (2019), 52–69, Section 4 (the root covering
  in the Puiseux theorem with parameters).
* S. G. Krantz, H. R. Parks, *A Primer of Real Analytic Functions*, second edition, Birkhäuser
  (2002), Chapter 2 (the analytic implicit function theorem).
-/

public section

open Filter Polynomial Set Topology

namespace TauCeti

namespace Polynomial

/-! ### Continuous roots of analytic families are analytic -/

section Analytic

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {F : E → 𝕜[X]} {x₀ : E} {d : ℕ}

/-- A family of polynomials whose coefficients are analytic at `x₀`, and whose degree stays at most
`d` near `x₀`, is analytic at `(x₀, z₀)` as a function of the parameter and the argument jointly. -/
theorem analyticAt_eval_of_analyticAt_coeff
    (hF : ∀ i ≤ d, AnalyticAt 𝕜 (fun x => (F x).coeff i) x₀)
    (hdeg : ∀ᶠ x in 𝓝 x₀, (F x).natDegree ≤ d) (z₀ : 𝕜) :
    AnalyticAt 𝕜 (fun v : E × 𝕜 => (F v.1).eval v.2) (x₀, z₀) := by
  have hsum : AnalyticAt 𝕜
      (fun v : E × 𝕜 => ∑ i ∈ Finset.range (d + 1), (F v.1).coeff i * v.2 ^ i) (x₀, z₀) :=
    Finset.analyticAt_fun_sum _ fun i hi => by
      have hi := (hF i (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi))).comp
        (analyticAt_fst (p := (x₀, z₀)))
      exact hi.fun_mul (analyticAt_snd.fun_pow i)
  refine hsum.congr ?_
  filter_upwards [continuousAt_fst.tendsto.eventually hdeg] with v hv
  exact (eval_eq_sum_range' (Nat.lt_succ_of_le hv) v.2).symm

/-- **A continuous root of an analytic family is analytic at a simple root.** Let `F` be a family
of polynomials with coefficients analytic at `x₀` and degree at most `d` near `x₀`. If `r` is
continuous at `x₀`, `r x` is a root of `F x` for all `x` near `x₀`, and `r x₀` is a simple root of
`F x₀`, then `r` is analytic at `x₀`.

In particular, the root coordinate `x ↦ (s x).1.2` of a continuous local section `s` of the root
space of such a family is analytic wherever the root it picks out is simple. -/
theorem analyticAt_of_eventually_isRoot [CompleteSpace 𝕜] [CompleteSpace E]
    (hF : ∀ i ≤ d, AnalyticAt 𝕜 (fun x => (F x).coeff i) x₀)
    (hdeg : ∀ᶠ x in 𝓝 x₀, (F x).natDegree ≤ d) {r : E → 𝕜} (hr : ContinuousAt r x₀)
    (hroot : ∀ᶠ x in 𝓝 x₀, (F x).IsRoot (r x))
    (hsimple : (derivative (F x₀)).eval (r x₀) ≠ 0) : AnalyticAt 𝕜 r x₀ := by
  obtain ⟨g, hga, -, -, hg⟩ :=
    (analyticAt_eval_of_analyticAt_coeff hF hdeg (r x₀)).exists_analyticAt_eventually_eq_zero_iff
      hroot.self_of_nhds (by simpa only [Polynomial.deriv] using hsimple)
  refine hga.congr ?_
  filter_upwards [(tendsto_id.prodMk_nhds hr).eventually hg, hroot] with x hx hxr
  exact hx.1 hxr

end Analytic

/-! ### The root space of a separable family is a covering space -/

section Covering

variable {𝕜 : Type*} [RCLike 𝕜]

/-- Near a coefficient tuple whose monic polynomial has `n` distinct roots, the roots of the nearby
monic polynomials are labelled by a tuple `Ψ c` which is continuous in `c` and pairwise distinct. -/
private theorem exists_monicOfCoeff_eq_prod_X_sub_C_mem_nhds {n : ℕ} {c₀ z : Fin n → 𝕜}
    (hz : Function.Injective z) (hc₀ : monicOfCoeff c₀ = ∏ i, (X - C (z i))) :
    ∃ Ψ : (Fin n → 𝕜) → Fin n → 𝕜, {c | ContinuousAt Ψ c ∧
      monicOfCoeff c = ∏ i, (X - C (Ψ c i)) ∧ Function.Injective (Ψ c)} ∈ 𝓝 c₀ := by
  obtain ⟨Ψ, hΨ₀, hΨa, hΨ⟩ := exists_analyticAt_monicOfCoeff_eq_prod_X_sub_C hz hc₀
  -- the labels stay pairwise distinct near `c₀`, being continuous and distinct at `c₀`
  have hne : ∀ i j : Fin n, ∀ᶠ c in 𝓝 c₀, i ≠ j → Ψ c i ≠ Ψ c j := by
    intro i j
    rcases eq_or_ne i j with rfl | hij
    · exact .of_forall fun _ h => absurd rfl h
    · have hi := (continuous_apply i).continuousAt.comp hΨa.continuousAt
      have hj := (continuous_apply j).continuousAt.comp hΨa.continuousAt
      filter_upwards [(hi.ne_iff_eventually_ne hj).1 (by simpa [hΨ₀] using hz.ne hij)] with
        c hc _ using hc
  refine ⟨Ψ, (hΨa.eventually_analyticAt.mono fun _ h => h.continuousAt).and (hΨ.and ?_)⟩
  filter_upwards [eventually_all.2 fun i => eventually_all.2 (hne i)] with c hc i j hij
  by_contra h
  exact hc i j h hij

variable [IsAlgClosed 𝕜] {B : Type*} [TopologicalSpace B] {F : B → 𝕜[X]} {d : ℕ}

/-- **The roots of a separable member can be labelled continuously nearby.** Let `F` be a family of
polynomials of constant degree `d` with continuous coefficients. Near a parameter `b₀` at which
`F b₀` is separable there are `d` continuous functions `σ i`, pairwise distinct at every
parameter, whose values are exactly the roots of `F b`. -/
theorem exists_continuousOn_isRoot_iff (hF : ∀ i ≤ d, Continuous fun b => (F b).coeff i)
    (hdeg : ∀ b, (F b).natDegree = d) {b₀ : B} (hsep : (F b₀).Separable) :
    ∃ U : Set B, IsOpen U ∧ b₀ ∈ U ∧ ∃ σ : Fin d → B → 𝕜, (∀ i, ContinuousOn (σ i) U) ∧
      ∀ b ∈ U, Function.Injective (fun i => σ i b) ∧ ∀ z, (F b).IsRoot z ↔ ∃ i, σ i b = z := by
  classical
  -- the leading coefficient `a b` is continuous and nonzero at `b₀`
  have ha : Continuous fun b => (F b).coeff d := hF d le_rfl
  have ha₀ : (F b₀).coeff d ≠ 0 := by
    simpa only [leadingCoeff, hdeg] using leadingCoeff_ne_zero.2 hsep.ne_zero
  have hopen : IsOpen {b | (F b).coeff d ≠ 0} := isOpen_compl_singleton.preimage ha
  -- the normalized lower coefficients `c b`, continuous where the leading coefficient is nonzero
  let c : B → Fin d → 𝕜 := fun b i => ((F b).coeff d)⁻¹ * (F b).coeff i
  have hc : ContinuousOn c {b | (F b).coeff d ≠ 0} := continuousOn_pi.2 fun i =>
    (ha.continuousOn.inv₀ fun _ hb => hb).mul (hF i i.2.le).continuousOn
  have hroot : ∀ b, (F b).coeff d ≠ 0 → ∀ z, (F b).IsRoot z ↔ (monicOfCoeff (c b)).IsRoot z := by
    intro b hb z
    have hmonic : (C ((F b).coeff d)⁻¹ * F b).Monic :=
      monic_C_mul_of_mul_leadingCoeff_eq_one (by rw [leadingCoeff, hdeg]; exact inv_mul_cancel₀ hb)
    have hnat : (C ((F b).coeff d)⁻¹ * F b).natDegree = d := by
      rw [natDegree_C_mul (inv_ne_zero hb), hdeg]
    have hc : monicOfCoeff (c b) = C ((F b).coeff d)⁻¹ * F b := by
      simpa only [coeff_C_mul] using monicOfCoeff_coeff hmonic hnat
    rw [hc, IsRoot, IsRoot, eval_mul, eval_C, mul_eq_zero, or_iff_right (inv_ne_zero hb)]
  -- an enumeration `z` of the `d` distinct roots of `F b₀`
  have hcard : (F b₀).roots.toFinset.card = d := by
    rw [Multiset.toFinset_card_of_nodup (nodup_roots hsep), IsAlgClosed.card_roots_eq_natDegree,
      hdeg]
  let e := (F b₀).roots.toFinset.equivFinOfCardEq hcard
  let z : Fin d → 𝕜 := fun i => e.symm i
  have hz : Function.Injective z := Subtype.val_injective.comp e.symm.injective
  have hc₀ : monicOfCoeff (c b₀) = ∏ i, (X - C (z i)) := by
    refine (Sym.toMonic_ofFn_eq_of_forall_isRoot (monic_monicOfCoeff _)
      (natDegree_monicOfCoeff _) hz fun i => (hroot b₀ ha₀ _).1 ?_).symm.trans (Sym.toMonic_ofFn z)
    exact (mem_roots hsep.ne_zero).1 (Multiset.mem_toFinset.1 (e.symm i).2)
  obtain ⟨Ψ, hW⟩ := exists_monicOfCoeff_eq_prod_X_sub_C_mem_nhds hz hc₀
  refine ⟨{b | (F b).coeff d ≠ 0} ∩ c ⁻¹' interior _, hc.isOpen_inter_preimage hopen
    isOpen_interior, ⟨ha₀, mem_interior_iff_mem_nhds.2 hW⟩, fun i b => Ψ (c b) i, ?_, ?_⟩
  · intro i b hb
    have hcb : ContinuousAt c b := hc.continuousAt (hopen.mem_nhds hb.1)
    exact ((continuous_apply i).continuousAt.comp
      ((interior_subset hb.2).1.comp hcb)).continuousWithinAt
  · intro b hb
    obtain ⟨-, hprod, hinjb⟩ := interior_subset hb.2
    refine ⟨hinjb, fun w => ?_⟩
    rw [hroot b hb.1, hprod]
    simp only [IsRoot.def, eval_prod, eval_sub, eval_X, eval_C, Finset.prod_eq_zero_iff,
      Finset.mem_univ, true_and, sub_eq_zero]
    exact exists_congr fun _ => eq_comm

/-- **The root space is evenly covered near a separable member.** For a family of polynomials of
constant degree `d` with continuous coefficients, the projection `(b, z) ↦ b` from the space of
pairs with `z` a root of `F b` is evenly covered, with fibre `Fin d`, near every parameter `b₀` at
which `F b₀` is separable. -/
theorem isEvenlyCovered_fst_isRoot (hF : ∀ i ≤ d, Continuous fun b => (F b).coeff i)
    (hdeg : ∀ b, (F b).natDegree = d) {b₀ : B} (hsep : (F b₀).Separable) :
    IsEvenlyCovered (fun q : {q : B × 𝕜 // (F q.1).IsRoot q.2} => q.1.1) b₀ (Fin d) := by
  obtain ⟨U, hU, hb₀, σ, hσc, hσ⟩ := exists_continuousOn_isRoot_iff hF hdeg hsep
  set f := fun q : {q : B × 𝕜 // (F q.1).IsRoot q.2} => q.1.1
  -- the label of a point of the root space over `U`: the sheet it lies on
  choose idx hidx using fun q : f ⁻¹' U => ((hσ _ q.2).2 q.1.1.2).1 q.1.2
  have hidx_iff : ∀ q i, idx q = i ↔ σ i q.1.1.1 = q.1.1.2 := fun q i =>
    ⟨fun h => h ▸ hidx q, fun h => (hσ _ q.2).1 ((hidx q).trans h.symm)⟩
  have hσq : ∀ i, Continuous fun q : f ⁻¹' U => σ i q.1.1.1 := fun i =>
    (hσc i).comp_continuous (by fun_prop) fun q => q.2
  -- the label is locally constant, since the sheets are pairwise disjoint and continuous
  have hidx_cont : Continuous idx := by
    refine continuous_discrete_rng.2 fun i => ?_
    have h : idx ⁻¹' {i} = ⋂ j, {q | j ≠ i → σ j q.1.1.1 ≠ q.1.1.2} := by
      ext q
      simp only [mem_preimage, mem_singleton_iff, mem_iInter, mem_ofPred_eq]
      constructor
      · rintro rfl j hj h
        exact hj ((hσ _ q.2).1 (h.trans (hidx q).symm))
      · intro h
        by_contra hne
        exact h _ hne (hidx q)
    rw [h]
    refine isOpen_iInter_of_finite fun j => ?_
    by_cases hj : j = i
    · simp [hj]
    · simpa [hj] using isOpen_ne_fun (hσq j) (by fun_prop)
  refine ⟨inferInstance, U, hb₀, hU, hU.preimage (by fun_prop),
    { toFun q := (⟨q.1.1.1, q.2⟩, idx q)
      invFun p := ⟨⟨(p.1.1, σ p.2 p.1.1), ((hσ _ p.1.2).2 _).2 ⟨p.2, rfl⟩⟩, p.1.2⟩
      left_inv q := Subtype.ext (Subtype.ext (Prod.ext rfl (hidx q)))
      right_inv p := Prod.ext rfl ((hidx_iff _ _).2 rfl)
      continuous_toFun := by fun_prop
      continuous_invFun := by
        refine Continuous.subtype_mk (Continuous.subtype_mk ?_ _) _
        refine (continuous_subtype_val.comp continuous_fst).prodMk ?_
        exact continuous_prod_of_discrete_right.2 fun i =>
          (hσc i).comp_continuous continuous_subtype_val fun x => x.2 }, fun _ => rfl⟩

/-- **The root space is a covering space over the separable members.** For a family of polynomials
of constant degree with continuous coefficients, the projection `(b, z) ↦ b` from the space of
pairs with `z` a root of `F b` is a covering map over the set of parameters `b` at which `F b` is
separable. -/
theorem isCoveringMapOn_fst_isRoot (hF : ∀ i ≤ d, Continuous fun b => (F b).coeff i)
    (hdeg : ∀ b, (F b).natDegree = d) :
    IsCoveringMapOn (fun q : {q : B × 𝕜 // (F q.1).IsRoot q.2} => q.1.1)
      {b | (F b).Separable} :=
  fun _ hb => (isEvenlyCovered_fst_isRoot hF hdeg hb).to_isEvenlyCovered_preimage

/-- **The root space of a separable family is a covering space.** For a family of separable
polynomials of constant degree with continuous coefficients, for instance a family of monic
polynomials whose discriminant vanishes nowhere, the projection `(b, z) ↦ b` from the space of
pairs with `z` a root of `F b` is a covering map. -/
theorem isCoveringMap_fst_isRoot (hF : ∀ i ≤ d, Continuous fun b => (F b).coeff i)
    (hdeg : ∀ b, (F b).natDegree = d) (hsep : ∀ b, (F b).Separable) :
    IsCoveringMap (fun q : {q : B × 𝕜 // (F q.1).IsRoot q.2} => q.1.1) :=
  fun b => (isEvenlyCovered_fst_isRoot hF hdeg (hsep b)).to_isEvenlyCovered_preimage

end Covering

/-! ### The fibres of the root space -/

section Fibre

variable {K : Type*} [CommRing K] [IsDomain K] {B : Type*} {F : B → K[X]}

/-- The fibre of the root space over `b` is the set of roots of `F b`: a point `(b, z)` of the
fibre corresponds to the root `z`. -/
@[expose, simps]
def preimageFstIsRootEquiv (F : B → K[X]) (b : B) :
    (fun q : {q : B × K // (F q.1).IsRoot q.2} => q.1.1) ⁻¹' {b} ≃ {z // (F b).IsRoot z} where
  toFun q := ⟨q.1.1.2, (mem_singleton_iff.1 q.2).subst (motive := fun b' => (F b').IsRoot q.1.1.2)
    q.1.2⟩
  invFun z := ⟨⟨(b, z.1), z.2⟩, rfl⟩
  left_inv q := Subtype.ext (Subtype.ext (Prod.ext (mem_singleton_iff.1 q.2).symm rfl))
  right_inv _ := rfl

/-- The fibre of the root space over a parameter `b` with `F b ≠ 0` is finite. -/
theorem finite_preimage_fst_isRoot {b : B} (hb : F b ≠ 0) :
    Finite ((fun q : {q : B × K // (F q.1).IsRoot q.2} => q.1.1) ⁻¹' {b}) :=
  have : Finite {z // (F b).IsRoot z} := (finite_setOfPred_isRoot hb).to_subtype
  .of_equiv _ (preimageFstIsRootEquiv F b).symm

/-- The fibre of the root space over a parameter `b` at which `F b` is separable of degree `d` has
exactly `d` points, over an algebraically closed field. -/
theorem natCard_preimage_fst_isRoot {K : Type*} [Field K] [IsAlgClosed K] {F : B → K[X]} {b : B}
    {d : ℕ} (hdeg : (F b).natDegree = d) (hsep : (F b).Separable) :
    Nat.card ((fun q : {q : B × K // (F q.1).IsRoot q.2} => q.1.1) ⁻¹' {b}) = d := by
  classical
  rw [Nat.card_congr ((preimageFstIsRootEquiv F b).trans
    (Equiv.subtypeEquivRight fun z => (Multiset.mem_toFinset.trans
      (mem_roots hsep.ne_zero)).symm)), Nat.card_eq_fintype_card, Fintype.card_coe,
    Multiset.toFinset_card_of_nodup (nodup_roots hsep), IsAlgClosed.card_roots_eq_natDegree, hdeg]

end Fibre

end Polynomial

end TauCeti
