/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GroupAlgGeom.Separated
public import TauCeti.GroupTheory.LimitGroup.CentralizerExtension.Discrimination
public import TauCeti.GroupTheory.LimitGroup.ResiduallyFree
import TauCeti.Topology.NoetherianSpace.Decomposition

/-!
# The centralizer of a generator and the union of two such centralizers

Let `F = F(α)` be a free group, viewed as a group over itself, and let `a, b` be free generators.
Over `F` the centralizer `⟨a⟩` of `a` is the algebraic set of the commutator equation
`[x, a] = 1` in one variable `x`, and the union `⟨a⟩ ∪ ⟨b⟩` is algebraic too: it is cut out by
the commutators `[[x, a], g [x, b] g⁻¹]`, `g ∈ F`
(`TauCeti.GroupAlgGeom.V_unionEquations_commutatorElement_of`; the variable may sit among any
number of other variables). In rank at least two this is because `F` is a domain; in rank one `F`
is abelian and both sets are everything.

The set `⟨a⟩` is irreducible in the Zariski topology. Its coordinate group is the extension
`F(a, ℤ) = F ∗_{⟨a⟩} ⟨a, t | [a, t]⟩` of the centralizer of `a`, the variable `x` going to the
new letter `t`; this group is discriminated by `F` over `F`, through the retractions `t ↦ aᵏ`,
and in particular fully residually free. For `a ≠ b` the union `⟨a⟩ ∪ ⟨b⟩` is reducible, with
the two irreducible components `⟨a⟩` and `⟨b⟩`. Its coordinate group, like every coordinate
group, is separated by `F` (`TauCeti.GroupAlgGeom.CoordGroup.isSeparatedBy_coeff`), and it
embeds in the product of the coordinate groups of the two components
(`TauCeti.GroupAlgGeom.CoordGroup.exists_injective_toPi_unionEquations`), but it is not
discriminated by `F`, and not even fully residually free: a fully residually free group is CSA,
and a CSA coordinate group over the nonabelian group `F` would make the union irreducible
(`TauCeti.GroupAlgGeom.isIrreducible_V_of_isCSA`).

## Main results

* `TauCeti.GroupAlgGeom.isIrreducible_setOf_mem_zpowers_of`: `⟨a⟩` is irreducible.
* `TauCeti.GroupAlgGeom.exists_bijective_gHom_coordGroup_centralizerExt`: the coordinate group
  of `[x, a] = 1` is `F(a, ℤ)` over `F`, with `x ↦ t`.
* `TauCeti.GroupAlgGeom.isDiscriminatedBy_coordGroup_singleton_commutatorElement_of`,
  `TauCeti.GroupAlgGeom.isFullyResiduallyFree_coordGroup_singleton_commutatorElement_of`: that
  coordinate group is discriminated by `F` and fully residually free.
* `TauCeti.GroupAlgGeom.V_unionEquations_commutatorElement_of`: `⟨a⟩ ∪ ⟨b⟩` is algebraic.
* `TauCeti.GroupAlgGeom.not_isIrreducible_setOf_mem_zpowers_of_or`,
  `TauCeti.GroupAlgGeom.maximal_isIrreducible_subset_setOf_mem_zpowers_of_or_iff`: for `a ≠ b`
  the union is reducible, and its irreducible components are `⟨a⟩` and `⟨b⟩`.
* `TauCeti.GroupAlgGeom.not_isDiscriminatedBy_coordGroup_unionEquations_commutatorElement_of`,
  `TauCeti.GroupAlgGeom.not_isFullyResiduallyFree_coordGroup_unionEquations_commutatorElement_of`:
  for `a ≠ b` the coordinate group of the union is neither discriminated by `F` nor fully
  residually free.

## References

* G. Baumslag, A. Myasnikov, V. Remeslennikov, *Algebraic geometry over groups I. Algebraic sets
  and ideal theory*, J. Algebra 219 (1999), §3.1 (Example 3, Lemma 6), §3.6 (Corollary 11,
  Proposition 12) and §4 (Lemma 15, Theorem 5).
* O. Kharlampovich, A. Myasnikov, *Irreducible affine varieties over a free group. I:
  Irreducibility of quadratic equations and Nullstellensatz*, J. Algebra 200 (1998), §3,
  Proposition 7.
* O. Kharlampovich, A. Myasnikov, *Implicit function theorem over free groups*, J. Algebra 290
  (2005), §§2.5–2.6.
-/

public section

namespace TauCeti.GroupAlgGeom

open Monoid.Coprod Subgroup FreeGroup LimitGroup
open scoped commutatorElement

variable {α X : Type*}

/-! ### The centralizer of a generator -/

/- Evaluation at a power `aᵏ` of a generator factors through the map `F[x] → F(a, ℤ)`, `x ↦ t`,
followed by the retraction `t ↦ aᵏ`. -/
private theorem eval_zpow_eq_retraction_comp (a : α) (k : ℤ) :
    eval (.id (FreeGroup α)) (fun _ : Unit => of a ^ k) =
      (CentralizerExt.retraction (u := of a) (n := 1) fun _ => k).comp
        (eval CentralizerExt.of fun _ : Unit => CentralizerExt.t 0) := by
  rw [MonoidHom.comp_eval, CentralizerExt.retraction_comp_of]
  simp [Function.comp_def]

/- The `F`-homomorphism `F[x] → F(a, ℤ)` sending `x` to the new letter `t`. -/
private def evalT (a : α) : GHom (inl : FreeGroup α →* GX (FreeGroup α) Unit)
    (CentralizerExt.of : FreeGroup α →* CentralizerExt (of a) 1) :=
  evalGHom CentralizerExt.of fun _ => CentralizerExt.t 0

private theorem mem_ker_evalT {a : α} {w : GX (FreeGroup α) Unit} :
    w ∈ (evalT a : GX (FreeGroup α) Unit →* CentralizerExt (of a) 1).ker ↔
      eval (CentralizerExt.of : FreeGroup α →* CentralizerExt (of a) 1)
        (fun _ => CentralizerExt.t 0) w = 1 := by
  simp [evalT]

/- The extension `F(a, ℤ)` of the centralizer of a generator is discriminated by `F`. -/
private theorem isDiscriminatedBy_centralizerExt_of (a : α) :
    IsDiscriminatedBy (CentralizerExt.of : FreeGroup α →* CentralizerExt (of a) 1) (.id _) :=
  CentralizerExt.isDiscriminatedBy FreeGroup.isBP IsFreeGroup.isCSA (of_ne_one a)

/- The points of `F` killed by the kernel of `F[x] → F(a, ℤ)`, `x ↦ t`, form `⟨a⟩`. -/
private theorem V_ker_evalT (a : α) :
    V (.id (FreeGroup α)) ((evalT a : GX (FreeGroup α) Unit →* CentralizerExt (of a) 1).ker :
      Set (GX (FreeGroup α) Unit)) = {v | v () ∈ zpowers (of a)} := by
  refine subset_antisymm (fun v hv => ?_) fun v hv => ?_
  · -- The new letter `t` commutes with `a`, so `[x, a]` lies in the kernel.
    have h : ⁅(inr (of ()) : GX (FreeGroup α) Unit), inl (of a)⁆ ∈
        (evalT a : GX (FreeGroup α) Unit →* CentralizerExt (of a) 1).ker := by
      rw [mem_ker_evalT]
      simpa [map_commutatorElement, commutatorElement_eq_one_iff_commute] using
        (CentralizerExt.commute_of_t (n := 1) (mem_centralizer_singleton_iff.2 rfl) 0).symm
    simpa [V_singleton_commutatorElement_of] using
      V_antitone (.id (FreeGroup α)) (Set.singleton_subset_iff.2 h) hv
  · -- At `x = aᵏ` evaluation factors through the retraction `t ↦ aᵏ`.
    obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hv
    obtain rfl : v = fun _ => of a ^ k := funext fun _ => hk.symm
    refine mem_V.2 fun w hw => ?_
    rw [eval_zpow_eq_retraction_comp, MonoidHom.comp_apply, mem_ker_evalT.1 hw, _root_.map_one]

/-- **The centralizer of a generator is irreducible.** Over a free group `F`, the cyclic subgroup
`⟨a⟩` generated by a free generator, the set of solutions of `[x, a] = 1`, is irreducible in the
Zariski topology on `F`. -/
theorem isIrreducible_setOf_mem_zpowers_of (a : α) :
    @IsIrreducible (Unit → FreeGroup α) (zariskiTopology (.id (FreeGroup α)) Unit)
      {v | v () ∈ zpowers (of a)} := by
  rw [← V_ker_evalT]
  exact (isDiscriminatedBy_centralizerExt_of a).isIrreducible_V_ker (evalT a)

/-- **The coordinate group of `[x, a] = 1` is an extension of a centralizer.** Over a free group
`F` and for a free generator `a`, the coordinate group of the equation `[x, a] = 1` is
isomorphic over `F` to the extension `F(a, ℤ) = F ∗_{⟨a⟩} ⟨a, t | [a, t]⟩` of the centralizer of
`a`, by an isomorphism sending `x` to the new letter `t`. -/
theorem exists_bijective_gHom_coordGroup_centralizerExt (a : α) :
    ∃ φ : GHom (CoordGroup.coeff (X := Unit) (.id (FreeGroup α))
        {⁅(inr (of ()) : GX (FreeGroup α) Unit), inl (of a)⁆})
        (CentralizerExt.of : FreeGroup α →* CentralizerExt (of a) 1), Function.Bijective φ ∧
      φ (QuotientGroup.mk (inr (of ()))) = CentralizerExt.t 0 := by
  -- `F(a, ℤ)` is separated by `F`, so `ker (x ↦ t)` is its own radical, with solutions `⟨a⟩`.
  have hker : Rad (.id (FreeGroup α)) {⁅(inr (of ()) : GX (FreeGroup α) Unit), inl (of a)⁆} =
      (evalT a : GX (FreeGroup α) Unit →* CentralizerExt (of a) 1).ker := by
    rw [Rad_def, V_singleton_commutatorElement_of, ← V_ker_evalT, ← Rad_def]
    exact (isDiscriminatedBy_centralizerExt_of a).isSeparatedBy.Rad_ker_eq (evalT a)
  -- `F(a, ℤ)` is generated by `F` and `t`.
  have hπ : Function.Surjective (evalT a) := by
    refine MonoidHom.range_eq_top.1 (eq_top_iff.2 ?_)
    rw [← CentralizerExt.closure_range_of_union_range_t, closure_le]
    rintro _ (⟨g, rfl⟩ | ⟨i, rfl⟩)
    · exact ⟨inl g, by simp [evalT]⟩
    · exact ⟨inr (of ()), by simp [evalT, Subsingleton.elim i 0]⟩
  obtain ⟨ψ, hψ, hψπ⟩ := GX.exists_bijective_gHom_of_eq_ker (evalT a) hπ hker
  rw [CoordGroup.coeff_def]
  exact ⟨ψ, hψ, by simpa [evalT] using hψπ (inr (of ()))⟩

/-- Over a free group `F` and for a free generator `a`, the coordinate group of `[x, a] = 1` is
discriminated by `F` over `F`. -/
theorem isDiscriminatedBy_coordGroup_singleton_commutatorElement_of (a : α) :
    IsDiscriminatedBy (CoordGroup.coeff (X := Unit) (.id (FreeGroup α))
      {⁅(inr (of ()) : GX (FreeGroup α) Unit), inl (of a)⁆}) (.id (FreeGroup α)) := by
  rw [← isIrreducible_V_iff_isDiscriminatedBy, V_singleton_commutatorElement_of]
  exact isIrreducible_setOf_mem_zpowers_of a

/-- Over a free group `F` and for a free generator `a`, the coordinate group of `[x, a] = 1` is
fully residually free. -/
theorem isFullyResiduallyFree_coordGroup_singleton_commutatorElement_of (a : α) :
    IsFullyResiduallyFree (CoordGroup (X := Unit) (.id (FreeGroup α))
      {⁅(inr (of ()) : GX (FreeGroup α) Unit), inl (of a)⁆}) :=
  (isFullyResiduallyFree_of_isFreeGroup (G := FreeGroup α)).of_isDiscriminatedBy
    (isDiscriminatedBy_coordGroup_singleton_commutatorElement_of a)

/-! ### The union of the centralizers of two generators -/

/-- **The union of two cyclic subgroups is algebraic.** Over a free group `F` and for free
generators `a` and `b`, the points whose `x`-coordinate lies in `⟨a⟩ ∪ ⟨b⟩` are the solutions of
the equations `[[x, a], g [x, b] g⁻¹] = 1`, `g ∈ F`. -/
theorem V_unionEquations_commutatorElement_of (x : X) (a b : α) :
    V (.id (FreeGroup α)) (unionEquations {⁅(inr (of x) : GX (FreeGroup α) X), inl (of a)⁆}
        {⁅(inr (of x) : GX (FreeGroup α) X), inl (of b)⁆}) =
      {v | v x ∈ zpowers (of a) ∨ v x ∈ zpowers (of b)} := by
  rcases subsingleton_or_nontrivial α with hα | hα
  · -- In rank one `F` is abelian: every commutator vanishes and `⟨a⟩ = C(a) = F`.
    have hc : IsMulCommutative (FreeGroup α) := FreeGroup.isMulCommutative_iff_subsingleton.2 hα
    have htop (c : α) (g : FreeGroup α) : g ∈ zpowers (of c) := by
      rw [← centralizer_singleton_of]
      exact mem_centralizer_singleton_iff.2 (mul_comm' _ _)
    ext v
    simp only [Set.mem_ofPred_eq, htop, or_self, iff_true, mem_V, mem_unionEquations]
    rintro _ ⟨_, rfl, _, rfl, g, rfl⟩
    simp [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm, mul_comm']
  · rw [V_unionEquations FreeGroup.isGDomain_id, V_singleton_commutatorElement_of,
      V_singleton_commutatorElement_of, Set.ofPred_or]

/- The cyclic subgroup `⟨c⟩`, in the `x`-coordinate, is Zariski closed. -/
private theorem isClosed_setOf_mem_zpowers_of (x : X) (c : α) :
    @IsClosed (X → FreeGroup α) (zariskiTopology (.id (FreeGroup α)) X)
      {v | v x ∈ zpowers (of c)} := by
  simpa [V_singleton_commutatorElement_of] using
    isClosed_V (X := X) (ι := .id (FreeGroup α)) {⁅(inr (of x) : GX (FreeGroup α) X), inl (of c)⁆}

/- If `⟨a⟩ ⊆ ⟨b⟩` in the `x`-coordinate, then `a = b`. -/
private theorem eq_of_setOf_mem_zpowers_subset (x : X) {a b : α}
    (h : {v : X → FreeGroup α | v x ∈ zpowers (of a)} ⊆ {v | v x ∈ zpowers (of b)}) : a = b := by
  obtain ⟨k, hk : of b ^ k = of a⟩ := mem_zpowers_iff.1 (@h (fun _ => of a) (mem_zpowers _))
  exact eq_of_commute_of_of (hk ▸ (Commute.refl (of b)).zpow_left k)

/-- **The union of two cyclic subgroups is reducible.** Over a free group `F` and for distinct
free generators `a` and `b`, the set of points whose `x`-coordinate lies in `⟨a⟩ ∪ ⟨b⟩` is not
irreducible in the Zariski topology. -/
theorem not_isIrreducible_setOf_mem_zpowers_of_or (x : X) {a b : α} (hab : a ≠ b) :
    ¬@IsIrreducible (X → FreeGroup α) (zariskiTopology (.id (FreeGroup α)) X)
      {v | v x ∈ zpowers (of a) ∨ v x ∈ zpowers (of b)} := by
  let := zariskiTopology (.id (FreeGroup α)) X
  intro h
  rcases isPreirreducible_iff_isClosed_union_isClosed.1 h.isPreirreducible _ _
    (isClosed_setOf_mem_zpowers_of x a) (isClosed_setOf_mem_zpowers_of x b) fun _ hv => hv
    with hsub | hsub
  · exact hab (eq_of_setOf_mem_zpowers_subset x fun v hv => hsub (Or.inr hv)).symm
  · exact hab (eq_of_setOf_mem_zpowers_subset x fun v hv => hsub (Or.inl hv))

/-- **The irreducible components of `⟨a⟩ ∪ ⟨b⟩`.** Over a free group `F` and for free generators
`a` and `b`, the maximal irreducible subsets of `⟨a⟩ ∪ ⟨b⟩ ⊆ F` are `⟨a⟩` and `⟨b⟩`. -/
theorem maximal_isIrreducible_subset_setOf_mem_zpowers_of_or_iff (a b : α)
    {Z : Set (Unit → FreeGroup α)} :
    Maximal (fun W => @IsIrreducible (Unit → FreeGroup α) (zariskiTopology (.id (FreeGroup α)) Unit)
        W ∧ W ⊆ {v | v () ∈ zpowers (of a) ∨ v () ∈ zpowers (of b)}) Z ↔
      Z = {v | v () ∈ zpowers (of a)} ∨ Z = {v | v () ∈ zpowers (of b)} := by
  let := zariskiTopology (.id (FreeGroup α)) Unit
  have hU : {v : Unit → FreeGroup α | v () ∈ zpowers (of a) ∨ v () ∈ zpowers (of b)} =
      ⋃ i, ![{v | v () ∈ zpowers (of a)}, {v | v () ∈ zpowers (of b)}] i := by
    ext
    simp [Fin.exists_fin_two]
  rw [hU, maximal_isIrreducible_subset_iUnion_iff
    (Fin.forall_fin_two.2 ⟨isClosed_setOf_mem_zpowers_of () a, isClosed_setOf_mem_zpowers_of () b⟩)
    (Fin.forall_fin_two.2 ⟨isIrreducible_setOf_mem_zpowers_of a,
      isIrreducible_setOf_mem_zpowers_of b⟩), Fin.exists_fin_two]
  -- Neither component lies in the other unless `a = b`, when they coincide.
  refine or_congr (and_iff_left_of_imp fun _ => Fin.forall_fin_two.2 ⟨fun h => h, ?_⟩)
    (and_iff_left_of_imp fun _ => Fin.forall_fin_two.2 ⟨?_, fun h => h⟩)
  all_goals
    intro h
    rw [eq_of_setOf_mem_zpowers_subset () h]
    exact subset_rfl

/-- Over a free group `F` and for distinct free generators `a` and `b`, the coordinate group of
the union `⟨a⟩ ∪ ⟨b⟩` (of the `x`-coordinate) is not discriminated by `F` over `F`, although it is
separated by `F` (`TauCeti.GroupAlgGeom.CoordGroup.isSeparatedBy_coeff`). -/
theorem not_isDiscriminatedBy_coordGroup_unionEquations_commutatorElement_of (x : X) {a b : α}
    (hab : a ≠ b) : ¬IsDiscriminatedBy (CoordGroup.coeff (X := X) (.id (FreeGroup α))
      (unionEquations {⁅(inr (of x) : GX (FreeGroup α) X), inl (of a)⁆}
        {⁅(inr (of x) : GX (FreeGroup α) X), inl (of b)⁆})) (.id (FreeGroup α)) := by
  rw [← isIrreducible_V_iff_isDiscriminatedBy, V_unionEquations_commutatorElement_of]
  exact not_isIrreducible_setOf_mem_zpowers_of_or x hab

/-- Over a free group `F` and for distinct free generators `a` and `b`, the coordinate group of
the union `⟨a⟩ ∪ ⟨b⟩` (of the `x`-coordinate) is not fully residually free. -/
theorem not_isFullyResiduallyFree_coordGroup_unionEquations_commutatorElement_of (x : X) {a b : α}
    (hab : a ≠ b) : ¬IsFullyResiduallyFree (CoordGroup (X := X) (.id (FreeGroup α))
      (unionEquations {⁅(inr (of x) : GX (FreeGroup α) X), inl (of a)⁆}
        {⁅(inr (of x) : GX (FreeGroup α) X), inl (of b)⁆})) := by
  -- A fully residually free group is CSA, and `a` and `b` do not commute.
  refine fun h => not_isIrreducible_setOf_mem_zpowers_of_or x hab ?_
  rw [← V_unionEquations_commutatorElement_of]
  refine isIrreducible_V_of_isCSA ⟨1, ?_⟩ h.isCSA (a := of a) (b := of b) fun hc =>
    hab (eq_of_commute_of_of hc)
  rw [V_unionEquations_commutatorElement_of]
  exact Or.inl (one_mem _)

end TauCeti.GroupAlgGeom
