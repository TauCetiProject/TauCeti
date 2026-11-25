/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Jacobson.Ring
public import Mathlib.RingTheory.Valuation.Integers
public import TauCeti.RingTheory.Valuation.Composite
import Mathlib.RingTheory.Valuation.LocalSubring
import TauCeti.RingTheory.Valuation.ValuationSubring

/-!
# Valuation subrings with residue field the constants

Let `K` be a field extension of a field `k`. The Zariski–Riemann space `ZR(K/k)` is the set of
valuation subrings of `K` containing `k`; a valuation subring specializes to the valuation
subrings it contains, so the closed points of `ZR(K/k)` are its minimal elements. This file shows
that valuation subrings whose residue field is algebraic over `k` are such closed points, and that
there are enough of them; over an algebraically closed `k` their residue field is `k`.

* A valuation subring `W ⊇ k` whose residue field `κ(W)` is algebraic over `k` is minimal among
  valuation subrings containing `k`: a valuation subring `V ⊆ W` is the composite of `W` with a
  valuation subring of `κ(W)` containing `k`, which is integrally closed and hence all of `κ(W)`.
  For example, for `K = ℝ(t)` the valuation ring at `t² + 1` has residue field `ℂ` and is minimal
  among valuation subrings containing `ℝ`.
* If `A ⊆ K` is a finitely generated `k`-subalgebra and `V₀` is a valuation subring of `K`
  containing `A`, then some valuation subring `W ⊆ V₀` containing `A` has residue field algebraic
  over `k`. Thus `W` is a closed point of `ZR(K/k)` in the closure of `V₀` and in the set of
  valuation subrings containing `A`. If `k` is algebraically closed, `W` has residue field `k`.

The second statement rests on two general facts: Zorn's lemma gives a valuation subring `W`
minimal among those between `A` and `V₀` (`ValuationSubring.exists_le_minimal`), and a field with
no proper valuation subring containing a finitely generated `k`-subalgebra is algebraic over `k`
(`Algebra.IsIntegral.of_forall_valuationSubring_eq_top`, a form of Zariski's lemma). Composite
valuation subrings (`ValuationSubring.comapResidue`) connect the two: for minimal `W`, the residue
field `κ(W)` has no proper valuation subring containing the image of `A`.

## Main results

* `ValuationSubring.sInfOfIsChain`: the intersection of a chain of valuation subrings.
* `ValuationSubring.exists_le_minimal`: below a valuation subring containing a set `s` there is a
  valuation subring minimal among those containing `s`.
* `Algebra.IsIntegral.of_forall_valuationSubring_eq_top`: a field with no proper valuation subring
  containing a given finitely generated subalgebra is algebraic over the base field.
* `ValuationSubring.eq_of_le_of_isIntegral_residueField`: a valuation subring with residue field
  algebraic over `k` is minimal among valuation subrings containing `k`.
* `ValuationSubring.exists_le_isIntegral_residueField`: a valuation subring containing a finitely
  generated `k`-subalgebra `A` contains a valuation subring containing `A` with residue field
  algebraic over `k`.
* `ValuationSubring.exists_le_bijective_algebraMap_residueField`: over an algebraically closed
  field `k`, that residue field is `k`.
* `ValuationSubring.exists_le_minimal_isTrivialOn`: consequently a valuation subring containing
  `A` contains a closed point of `ZR(K/k)` containing `A`.

## References

* P. Scholze, *Étale cohomology of diamonds*, proof of Proposition 25.4.
-/

public section

open IsLocalRing

namespace ValuationSubring

variable {K : Type*} [Field K]

/-- The intersection of a chain `c` of valuation subrings of `K`, as a valuation subring. (For the
empty chain it is `K` itself.) -/
def sInfOfIsChain (c : Set (ValuationSubring K)) (hc : IsChain (· ≤ ·) c) : ValuationSubring K :=
  ofSubring (⨅ W : c, W.val.toSubring) fun x ↦ by
    simp only [Subring.mem_iInf, Subtype.forall, mem_toSubring]
    by_cases hx : ∀ W ∈ c, x ∈ W
    · exact .inl hx
    push Not at hx
    obtain ⟨W₁, hW₁, hxW₁⟩ := hx
    refine .inr fun W hW ↦ ?_
    rcases hc.total hW₁ hW with h | h
    · exact h ((W₁.mem_or_inv_mem x).resolve_left hxW₁)
    · exact (W.mem_or_inv_mem x).resolve_left fun hxW ↦ hxW₁ (h hxW)

/-- The elements of the intersection of a chain are those lying in every member. -/
theorem mem_sInfOfIsChain_iff {c : Set (ValuationSubring K)} {hc : IsChain (· ≤ ·) c} {x : K} :
    x ∈ sInfOfIsChain c hc ↔ ∀ W ∈ c, x ∈ W := by
  simp [sInfOfIsChain, mem_ofSubring, Subring.mem_iInf]

/-- Below a valuation subring `V₀` containing a set `s` there is a valuation subring which is
minimal among the valuation subrings containing `s`. -/
theorem exists_le_minimal (V₀ : ValuationSubring K) {s : Set K} (hs : s ⊆ V₀) :
    ∃ W ≤ V₀, Minimal (fun W : ValuationSubring K ↦ s ⊆ W) W :=
  zorn_ge_nonempty₀ {W : ValuationSubring K | s ⊆ W} (fun c hcs hc _ _ ↦
    ⟨sInfOfIsChain c hc.symm, fun _ hx ↦ mem_sInfOfIsChain_iff.mpr fun _ hW ↦ hcs hW hx,
      fun _ hW _ hx ↦ mem_sInfOfIsChain_iff.mp hx _ hW⟩) V₀ hs

end ValuationSubring

/-- **Zariski's lemma for valuation subrings.** Let `B` be a finitely generated subalgebra of a
field extension `K` of `k`. If the only valuation subring of `K` containing `B` is `K` itself,
then `K` is algebraic over `k`. -/
theorem Algebra.IsIntegral.of_forall_valuationSubring_eq_top {k K : Type*} [Field k] [Field K]
    [Algebra k K] {B : Subalgebra k K} (hB : B.FG)
    (h : ∀ W : ValuationSubring K, (B : Set K) ⊆ W → W = ⊤) : Algebra.IsIntegral k K := by
  refine ⟨fun y ↦ ?_⟩
  -- `R = B[y]` lies in no proper valuation subring, so it is a field
  let R := B ⊔ Algebra.adjoin k {y}
  have hR : IsField R := R.val.toRingHom.isField_of_forall_valuationSubring_eq_top
    Subtype.val_injective fun W hW ↦ h W fun b hb ↦ hW ⟨b, le_sup_left (a := B) hb⟩
  let := hR.toField
  -- by Zariski's lemma the finitely generated field `R` is finite over `k`
  have : Algebra.FiniteType k R :=
    (Subalgebra.fg_iff_finiteType R).mp (hB.sup ⟨{y}, by rw [Finset.coe_singleton]⟩)
  have := finite_of_finite_type_of_isJacobsonRing k R
  have hy : y ∈ R := le_sup_right (a := B) (Algebra.subset_adjoin rfl)
  exact (Algebra.IsIntegral.isIntegral (R := k) (⟨y, hy⟩ : R)).map R.val

namespace ValuationSubring

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

/-- **Valuation subrings with algebraic residue field are closed points of `ZR(K/k)`.** If a
valuation subring `W` of `K` contains `k` and its residue field is algebraic over `k`, then every
valuation subring `V ⊆ W` containing `k` equals `W`. In particular this applies when the residue
field of `W` is `k`. -/
theorem eq_of_le_of_isIntegral_residueField (V : ValuationSubring K) {W : ValuationSubring K}
    [V.valuation.IsTrivialOn k] [W.valuation.IsTrivialOn k] [Algebra.IsIntegral k (ResidueField W)]
    (hVW : V ≤ W) : V = W := by
  obtain ⟨U, rfl⟩ := exists_comapResidue_eq hVW
  refine comapResidue_eq_self_iff.mpr (_root_.eq_top_iff.mpr fun y _ ↦ ?_)
  -- `U` contains the residues of the constants, so it is integrally closed in the algebraic
  -- extension `κ(W)` of `k`
  have : U.valuation.IsTrivialOn k := .of_le_one _ fun c ↦ by
    rw [valuation_le_one_iff, IsScalarTower.algebraMap_apply k W (ResidueField W),
      ResidueField.algebraMap_eq, ← coe_mem_comapResidue_iff, coe_algebraMap_of_isTrivialOn]
    exact algebraMap_mem_of_isTrivialOn _ c
  obtain ⟨u, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.mp
    ((Algebra.IsIntegral.isIntegral (R := k) y).tower_top (A := U))
  exact u.property

/-- **Existence of valuation subrings with algebraic residue field.** Let `A` be a finitely
generated `k`-subalgebra of `K` and `V₀` a valuation subring of `K` containing `A`. Then some
valuation subring `W ⊆ V₀` of `K` containing `A` has residue field algebraic over `k`. -/
theorem exists_le_isIntegral_residueField (V₀ : ValuationSubring K) {A : Subalgebra k K}
    (hA : A.FG) (hAV₀ : (A : Set K) ⊆ V₀) :
    ∃ (W : ValuationSubring K) (_ : W.valuation.IsTrivialOn k), W ≤ V₀ ∧ (A : Set K) ⊆ W ∧
      Algebra.IsIntegral k (ResidueField W) := by
  obtain ⟨W, hWV₀, hmin⟩ := V₀.exists_le_minimal hAV₀
  have hAW : (A : Set K) ⊆ W := hmin.prop
  have : W.valuation.IsTrivialOn k := .of_le_one _ fun c ↦
    (W.valuation_le_one_iff _).mpr (hAW (A.algebraMap_mem c))
  refine ⟨W, this, hWV₀, hAW, ?_⟩
  -- the image `B` of `A` in `κ(W)` lies in no proper valuation subring of `κ(W)`, since its
  -- composite with `W` would be a smaller valuation subring containing `A`
  let f : A →ₐ[k] ResidueField W := (IsScalarTower.toAlgHom k W (ResidueField W)).comp
    ⟨A.val.toRingHom.codRestrict W fun a ↦ hAW a.property, fun c ↦
      Subtype.ext (W.coe_algebraMap_of_isTrivialOn c).symm⟩
  have hf (a : A) : f a = residue W ⟨a, hAW a.property⟩ := by
    simp only [f, AlgHom.comp_apply, IsScalarTower.coe_toAlgHom', ResidueField.algebraMap_eq]
    exact congrArg (residue W) (Subtype.ext (by simp))
  have hfg : (⊤ : Subalgebra k A).FG := ((Subalgebra.fg_iff_finiteType A).mp hA).out
  refine .of_forall_valuationSubring_eq_top (hfg.map f) fun U hU ↦ ?_
  refine (comapResidue_eq_self_iff (A := W)).mp (hmin.eq_of_le (fun a ha ↦ ?_) comapResidue_le)
  exact coe_mem_comapResidue_iff (a := ⟨a, hAW ha⟩).mpr
    (hf ⟨a, ha⟩ ▸ hU (Subalgebra.mem_map.mpr ⟨⟨a, ha⟩, trivial, rfl⟩))

/-- **Existence of valuation subrings with residue field `k`.** Let `k` be algebraically closed,
`A` a finitely generated `k`-subalgebra of `K` and `V₀` a valuation subring of `K` containing `A`.
Then some valuation subring `W ⊆ V₀` of `K` containing `A` has residue field `k`. -/
theorem exists_le_bijective_algebraMap_residueField [IsAlgClosed k] (V₀ : ValuationSubring K)
    {A : Subalgebra k K} (hA : A.FG) (hAV₀ : (A : Set K) ⊆ V₀) :
    ∃ (W : ValuationSubring K) (_ : W.valuation.IsTrivialOn k), W ≤ V₀ ∧ (A : Set K) ⊆ W ∧
      Function.Bijective (algebraMap k (ResidueField W)) :=
  (V₀.exists_le_isIntegral_residueField hA hAV₀).imp fun _ ⟨h, hWV₀, hAW, _⟩ ↦
    ⟨h, hWV₀, hAW, IsAlgClosed.algebraMap_bijective_of_isIntegral⟩

/-- **Closed points of `ZR(K/k)` below a point.** Let `A` be a finitely generated `k`-subalgebra
of `K` and `V₀` a valuation subring of `K` containing `A`. Then some valuation subring `W ⊆ V₀`
containing `A` is minimal among the valuation subrings of `K` containing `k`. -/
theorem exists_le_minimal_isTrivialOn (V₀ : ValuationSubring K) {A : Subalgebra k K} (hA : A.FG)
    (hAV₀ : (A : Set K) ⊆ V₀) :
    ∃ W ≤ V₀, (A : Set K) ⊆ W ∧
      Minimal (fun V : ValuationSubring K ↦ V.valuation.IsTrivialOn k) W := by
  obtain ⟨W, _, hWV₀, hAW, _⟩ := V₀.exists_le_isIntegral_residueField hA hAV₀
  exact ⟨W, hWV₀, hAW, ‹_›, fun V _ hVW ↦ (V.eq_of_le_of_isIntegral_residueField (k := k) hVW).ge⟩

end ValuationSubring
