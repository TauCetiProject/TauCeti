/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.QuadraticForm.Global.Existence
public import TauCeti.NumberTheory.QuadraticForm.Global.FormInvariants
public import TauCeti.NumberTheory.QuadraticForm.Global.LocalRealization
public import TauCeti.NumberTheory.QuadraticForm.Global.SignPrescription
import TauCeti.NumberTheory.QuadraticForm.Global.Classification
import TauCeti.NumberTheory.QuadraticForm.Global.DiagonalApproximation
import TauCeti.NumberTheory.QuadraticForm.Global.Discrepancy
import TauCeti.NumberTheory.QuadraticForm.Global.HasseSupport
import TauCeti.NumberTheory.QuadraticForm.Global.Nonsquare
import TauCeti.NumberTheory.QuadraticForm.Global.ProductFormula

/-!
# Global forms with prescribed local behavior, up to one representation

Let `I` be an admissible system of local invariants of rank `n` over a number field `K`, and let
`U_v` (at the finite places) and `R_w` (at the real places) be regular local forms realizing `I`.
O'Meara's existence theorem 72:1 produces a regular global form isometric to `U_v` and `R_w` at
every place. This file carries out its construction up to the one step that needs the local-global
principle for representations.

1. A regular global form `W` of rank `n` with the global discriminant of `I` is chosen isometric to
   `R_w` at every real place, by approximating diagonal coefficients.
2. The finite places where `W_v` and `U_v` are not isometric are those where their Hasse signs
   differ. There are finitely many of them, and an even number, because both Hasse products are
   one and the real Hasse signs agree.
3. Weak approximation gives `β ∈ Kˣ` positive at every real place and a nonsquare at each of these
   places, and Hilbert sign prescription gives `α ∈ Kˣ` with `(α, β)_v = -1` exactly there.

So `W_v ≅ U_v` exactly when `(α, β)_v = 1`. With the correction planes `P = ⟨1, -β⟩` and
`P' = ⟨α, -αβ⟩`, the plane `P'` is then represented by `P ⊥ W` at every finite and real place, and
any representation of `P'` by `P ⊥ W` over `K` yields a regular global form whose system of local
invariants is `I`.

The Hasse product formula for `W` is Hilbert reciprocity
(`QuadraticForm.globalInvariants_hasseProduct_eq_one`), and the choice of `α` is Hilbert sign
prescription (`TauCeti.NumberField.QuadraticForm.exists_hilbertSymbol_eq_ite`), so both steps hold
over every number field.

## Main results

Both results are in the namespace `TauCeti.NumberField.QuadraticForm.GlobalFormInvariants`.

* `IsLocalRealization.exists_atFinitePlace_equivalent_iff_hilbertSymbol_eq_one`:
  a first global approximation `W` and elements `α, β` with `W_v ≅ U_v ↔ (α, β)_v = 1` at every
  finite place, `W_w ≅ R_w` at every real place and `β` positive at every real place.
* `IsLocalRealization.exists_locallyRepresents_prod`:
  `⟨α, -αβ⟩` is locally represented by `⟨1, -β⟩ ⊥ W`, and a global representation gives a regular
  global form whose system of local invariants is `I`.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms*, Springer (1963), 72:1, with 71:19a for the
  choice of `α`.
-/

public section

open IsDedekindDomain NumberField NumberField.InfinitePlace QuadraticMap TauCeti

namespace TauCeti.NumberField.QuadraticForm.GlobalFormInvariants.IsLocalRealization

variable {K : Type} [Field K] [NumberField K] {I : GlobalFormInvariants K}
  {U : ∀ v : HeightOneSpectrum (𝓞 K),
    _root_.QuadraticForm (v.adicCompletion K) (Fin I.rank → v.adicCompletion K)}
  {R : {w : InfinitePlace K // w.IsReal} → _root_.QuadraticForm ℝ (Fin I.rank → ℝ)}

/-- **The approximation and correction data of O'Meara 72:1.** Let `U_v` and `R_w` be local forms
realizing an admissible system `I`. Then there are a regular global form `W` of rank `I.rank` with
the global discriminant of `I`, isometric to `R_w` at every real place, and `α, β ∈ Kˣ`, with `β`
positive at every real place, such that `W_v ≅ U_v` exactly when `(α, β)_v = 1`, at every finite
place `v`. -/
theorem exists_atFinitePlace_equivalent_iff_hilbertSymbol_eq_one
    (hI : I.IsAdmissible) (hL : I.IsLocalRealization U R) :
    ∃ (W : _root_.QuadraticForm K (Fin I.rank → K)) (hW : W.Nondegenerate) (a b : Kˣ),
      (letI : Invertible (2 : K) := invertibleOfNonzero two_ne_zero;
        RegularFormClass.discr (formClass W hW) = I.discr) ∧
      (∀ w, (W.atRealPlace w).Equivalent (R w)) ∧
      (∀ w : {w : InfinitePlace K // w.IsReal}, 0 < embedding_of_isReal w.2 (b : K)) ∧
      ∀ v, (W.atFinitePlace v).Equivalent (U v) ↔
        hilbertSymbol (v.unitAtFinitePlace a) (v.unitAtFinitePlace b) = 1 := by
  classical
  let : Invertible (2 : K) := invertibleOfNonzero two_ne_zero
  -- Step 1: a global form with the discriminant of `I`, matching `R` at every real place.
  obtain ⟨W, hW, hWd, -, hWR⟩ := exists_form_discr_eq_equivalent_at_places hI.one_le_rank ∅
    Finset.univ (Additive.toMul (Quotient.out I.discr))
    (fun v ↦ (Finset.notMem_empty _ v.2).elim) (fun w ↦ R w.1)
    (fun v ↦ (Finset.notMem_empty _ v.2).elim) (fun w ↦ hL.nondegenerate_real w.1)
    (fun v ↦ (Finset.notMem_empty _ v.2).elim)
    (fun w ↦ by rw [hL.discr_real hI, discrAtRealPlace_def, squareClass_toMul_out])
  rw [squareClass_toMul_out] at hWd
  have hWR' (w : {w : InfinitePlace K // w.IsReal}) : (W.atRealPlace w).Equivalent (R w) :=
    hWR ⟨w, Finset.mem_univ w⟩
  -- Step 2: the places where `W_v` and `U_v` differ are those where the Hasse signs differ; they
  -- are finitely many, and an even number by the two Hasse product formulas.
  have hJ : (W.globalInvariants hW).hasseProduct = 1 := W.globalInvariants_hasseProduct_eq_one hW
  have hreal (w : {w : InfinitePlace K // w.IsReal}) :
      I.realHasse w = (W.globalInvariants hW).realHasse w := by
    simp [(hL.atRealPlace_equivalent_iff_realPositiveIndex_eq hW (by simp) w).mp (hWR' w)]
  let S := hI.hasFiniteMulSupport_finiteHasse.toFinset ∪
    (W.hasFiniteMulSupport_finiteHasse hW).toFinset
  let T := S.filter fun v ↦ I.finiteHasse v ≠ W.finiteHasse hW v
  have hT : Even T.card := by
    simpa only [QuadraticForm.globalInvariants_finiteHasse] using
      even_card_finiteHasse_ne I _ hI.hasseProduct_eq_one hJ hreal
        (fun v hv ↦ Finset.mem_union_left _ (Set.Finite.mem_toFinset _ |>.mpr hv))
        (fun v hv ↦ Finset.mem_union_right _ (Set.Finite.mem_toFinset _ |>.mpr
          (by rwa [QuadraticForm.globalInvariants_finiteHasse] at hv)))
  have hmemT (v : HeightOneSpectrum (𝓞 K)) : v ∈ T ↔ I.finiteHasse v ≠ W.finiteHasse hW v := by
    refine ⟨fun hv ↦ (Finset.mem_filter.mp hv).2, fun hv ↦ Finset.mem_filter.mpr ⟨?_, hv⟩⟩
    -- Outside `S` both Hasse signs are one.
    by_contra hS
    have hI1 : I.finiteHasse v = 1 := not_not.mp fun h1 ↦
      hS (Finset.mem_union_left _ (Set.Finite.mem_toFinset _ |>.mpr h1))
    have hW1 : W.finiteHasse hW v = 1 := not_not.mp fun h1 ↦
      hS (Finset.mem_union_right _ (Set.Finite.mem_toFinset _ |>.mpr h1))
    exact hv (hI1.trans hW1.symm)
  -- Step 3: `β` positive at every real place and a nonsquare on `T`, and `α` with
  -- `(α, β)_v = -1` exactly on `T`.
  obtain ⟨b, hbT, -, hb⟩ := exists_fieldUnit_not_isSquare_at_places T ∅
  obtain ⟨a, ha, -⟩ := exists_hilbertSymbol_eq_ite b T ∅
    (fun v hv ↦ (hbT v hv).2) (by simp) (by simpa using hT)
  refine ⟨W, hW, a, b, hWd, hWR', fun w ↦ hb w (Finset.notMem_empty w), fun v ↦ ?_⟩
  rw [hL.atFinitePlace_equivalent_iff_finiteHasse_eq (by simp) hWd, ha, eq_comm]
  by_cases hv : v ∈ T
  · simp [hv, (hmemT v).mp hv]
  · simpa [hv] using not_not.mp ((hmemT v).not.mp hv)

/-- **O'Meara 72:1 up to one global representation.** Let `U_v` and `R_w` be local forms realizing
an admissible system `I`. Then there are a regular global form `W` of rank `I.rank` and
`α, β ∈ Kˣ` such that `⟨α, -αβ⟩` is represented by `⟨1, -β⟩ ⊥ W` at every finite and real place,
and such that, if `⟨α, -αβ⟩` is represented by `⟨1, -β⟩ ⊥ W` over `K`, some regular global form on
`K ^ I.rank` has `I` as its system of local invariants. -/
theorem exists_locallyRepresents_prod
    (hI : I.IsAdmissible) (hL : I.IsLocalRealization U R) :
    ∃ (W : _root_.QuadraticForm K (Fin I.rank → K)) (_ : W.Nondegenerate) (a b : Kˣ),
      QuadraticForm.LocallyRepresents (weightedSumSquares K ![(a : K), -(a * b : K)])
        ((weightedSumSquares K ![1, -(b : K)]).prod W) ∧
      ((weightedSumSquares K ![(a : K), -(a * b : K)]).IsRepresentedBy
          ((weightedSumSquares K ![1, -(b : K)]).prod W) →
        ∃ (Q : _root_.QuadraticForm K (Fin I.rank → K)) (hQ : Q.Nondegenerate),
          Q.globalInvariants hQ = I) := by
  let : Invertible (2 : K) := invertibleOfNonzero two_ne_zero
  obtain ⟨W, hW, a, b, hWd, hWR, hb, hWU⟩ :=
    exists_atFinitePlace_equivalent_iff_hilbertSymbol_eq_one hI hL
  have hUd (v : HeightOneSpectrum (𝓞 K)) : (algebraMap K (v.adicCompletion K)).squareClassMap
      (RegularFormClass.discr (formClass W hW)) =
        RegularFormClass.discr (formClass _ (hL.nondegenerate_finite v)) := by
    rw [hL.discr_finite, discrAtFinitePlace_def, hWd]
  refine ⟨W, hW, a, b, QuadraticForm.locallyRepresents_weightedSumSquares_neg_self_mul_prod hW
    a b hb (Module.finrank_fin_fun K) U hL.nondegenerate_finite hUd
    fun v hv ↦ (hWU v).not.mpr (by simp [hv]), fun hrep ↦ ?_⟩
  obtain ⟨Q, hQ, hQd, hQU, hQR⟩ :=
    QuadraticForm.exists_discr_eq_equivalent_of_isRepresentedBy_prod hW a b hb
      (Module.finrank_fin_fun K) U hL.nondegenerate_finite hUd hWU hrep
  rw [hWd] at hQd
  refine ⟨Q, hQ, GlobalFormInvariants.ext (by simp) ?_ (funext fun v ↦ ?_) (funext fun w ↦ ?_)⟩
  · rw [QuadraticForm.globalInvariants_discr, hQd]
  · rw [QuadraticForm.globalInvariants_finiteHasse]
    exact (hL.atFinitePlace_equivalent_iff_finiteHasse_eq (by simp) hQd v).mp (hQU v)
  · rw [QuadraticForm.globalInvariants_realPositiveIndex]
    exact (hL.atRealPlace_equivalent_iff_realPositiveIndex_eq hQ (by simp) w).mp
      ((hQR w).trans (hWR w))

end TauCeti.NumberField.QuadraticForm.GlobalFormInvariants.IsLocalRealization
