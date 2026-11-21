/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Kaehler.Basic
public import TauCeti.FieldTheory.Frobenius.PBasis
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition

/-!
# `p`-bases and Kähler differentials

Let `k` be a field of prime characteristic `p` and `R` a commutative ring with an algebra map into
`k` whose image lies in the Frobenius subfield `k ^ p = (frobenius k p).fieldRange` (for instance,
`R = ℤ`, `R = ZMod p`, `R = k ^ p`, or any perfect ring `R` of characteristic `p`).

Every `R`-derivation out of `k` vanishes on `k ^ p`, so `Ω[k⁄R]` is canonically isomorphic to
`Ω[k⁄k ^ p]`. From a `p`-basis `b : ι → k`, differentiating `p`-monomials defines coordinate
`k ^ p`-derivations `δ_j : k → k` with `δ_j (b i) = δ_{ij}`, showing that `D R k ∘ b` is a
`k`-basis of `Ω[k⁄R]`. Combining this with the existence of possibly infinite `p`-bases yields the
equivalences between `p`-independence and `k`-linear independence of differentials, between
`p`-bases and `k`-bases of `Ω[k⁄R]`, the kernel identification `ker (D R k) = k ^ p`, the
finiteness criterion `FiniteDimensional k Ω[k⁄R] ↔ FiniteDimensional (frobenius k p).fieldRange k`,
and the degree formula `[k : k ^ p] = p ^ dim_k Ω[k⁄R]`.

## Main definitions

* `TauCeti.kaehlerEquivFrobeniusRange`: the canonical `k`-linear equivalence
  `Ω[k⁄R] ≃ₗ[k] Ω[k⁄(frobenius k p).fieldRange]`.
* `TauCeti.IsPBasis.coordDerivation`: the coordinate `k ^ p`-derivation associated to a member of a
  `p`-basis.
* `TauCeti.IsPBasis.kaehlerBasis`: the `k`-basis `i ↦ D R k (b i)` of `Ω[k⁄R]` associated to a
  `p`-basis `b`.

## Main results

* `TauCeti.isPIndependent_iff_linearIndependent_D`: a family is `p`-independent iff its
  differentials are linearly independent over `k`.
* `TauCeti.isPBasis_iff_linearIndependent_and_span_D`: a family is a `p`-basis iff its
  differentials form a `k`-basis of `Ω[k⁄R]`.
* `TauCeti.D_eq_zero_iff_mem_fieldRange_frobenius`: `D R k x = 0 ↔ x ∈ (frobenius k p).fieldRange`.
* `TauCeti.kaehler_finiteDimensional_iff`: `Ω[k⁄R]` is finite-dimensional over `k` iff `k` is
  finite-dimensional over `k ^ p`.
* `TauCeti.finrank_fieldRange_frobenius_eq_pow_finrank_kaehler`:
  `[k : k ^ p] = p ^ Module.finrank k Ω[k⁄R]` when `[k : k ^ p]` is finite.
* `TauCeti.subsingleton_kaehlerDifferential_iff_perfectRing`: `Ω[k⁄R]` vanishes iff `k` is perfect.

## References

* D. Clausen, A. Mathew, M. Morrow, *K-theory and topological cyclic homology of henselian pairs*,
  J. Amer. Math. Soc. 34 (2021), §5.1, Footnote 10.
* H. Matsumura, *Commutative Ring Theory*, second edition, Cambridge University Press, 1989, §26.
* The Stacks Project, Algebra, Definition 15.47.1 (Tag 07P1) and Lemma 15.47.2 (Tag 07P2).
-/

public section

noncomputable section

open KaehlerDifferential

namespace TauCeti

section BaseRing

/-- If `R` is a perfect ring of characteristic `p`, its image in any field `k` of exponential
characteristic `p` lies in the Frobenius subfield `k ^ p`. -/
theorem algebraMap_mem_fieldRange_frobenius_of_perfectRing (p : ℕ) {R k : Type*}
    [CommSemiring R] [Field k] [ExpChar k p] [Algebra R k] [PerfectRing R p] (r : R) :
    algebraMap R k r ∈ (frobenius k p).fieldRange := by
  obtain ⟨s, rfl⟩ := (PerfectRing.bijective_frobenius (R := R) (p := p)).2 r
  exact ⟨algebraMap R k s, by rw [frobenius_def, map_pow]⟩

/-- The image of `ℤ` in any field `k` of exponential characteristic `p` lies in `k ^ p`. -/
theorem intCast_mem_fieldRange_frobenius (p : ℕ) {k : Type*} [Field k] [ExpChar k p] (n : ℤ) :
    algebraMap ℤ k n ∈ (frobenius k p).fieldRange :=
  ⟨algebraMap ℤ k n, by rw [eq_intCast, map_intCast]⟩

variable {p : ℕ} [Fact p.Prime] {R k : Type*} [CommRing R] [Field k] [CharP k p] [Algebra R k]

/-- Every element of the Frobenius subfield `k ^ p` has vanishing universal differential over any
commutative base ring `R`. -/
theorem D_eq_zero_of_mem_fieldRange_frobenius {x : k} (hx : x ∈ (frobenius k p).fieldRange) :
    D R k x = 0 := by
  obtain ⟨a, rfl⟩ := hx
  rw [frobenius_def, Derivation.leibniz_pow, ← Nat.cast_smul_eq_nsmul k, CharP.cast_eq_zero,
    zero_smul]

/-- For any family `b : ι → k`, every element of the intermediate field `k ^ p(range b)` has
differential in the `k`-linear span of `{D R k (b i)}`. -/
theorem D_mem_span_D_of_mem_adjoin {ι : Type*} (b : ι → k) {x : k}
    (hx : x ∈ IntermediateField.adjoin (frobenius k p).fieldRange (Set.range b)) :
    D R k x ∈ Submodule.span k (Set.range fun i ↦ D R k (b i)) := by
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  set S : Submodule k Ω[k⁄R] := Submodule.span k (Set.range fun i ↦ D R k (b i))
  change x ∈ (IntermediateField.adjoin (frobenius k p).fieldRange (Set.range b)).toSubmodule at hx
  rw [← span_range_pMonomial_eq_adjoin] at hx
  induction hx using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨e, rfl⟩ := hu
    rw [pMonomial_def, Finsupp.prod]
    induction e.support using Finset.cons_induction with
    | empty => simp
    | cons i s hi ih =>
      rw [Finset.prod_cons, Derivation.leibniz]
      refine S.add_mem (S.smul_mem _ ih) (S.smul_mem _ ?_)
      rw [Derivation.leibniz_pow, ← Nat.cast_smul_eq_nsmul k]
      exact S.smul_mem _ (S.smul_mem _ (Submodule.subset_span ⟨i, rfl⟩))
  | zero => simp
  | add u v _ _ hu hv => rw [map_add]; exact S.add_mem hu hv
  | smul c u _ hu =>
    change D R k ((c : k) * u) ∈ S
    rw [Derivation.leibniz, D_eq_zero_of_mem_fieldRange_frobenius c.2, smul_zero, add_zero]
    exact S.smul_mem (c : k) hu

variable (p R k)

/-- The canonical `k`-linear equivalence `Ω[k⁄R] ≃ₗ[k] Ω[k⁄k ^ p]` when the image of `R` in `k`
lies in the Frobenius subfield `k ^ p`. -/
def kaehlerEquivFrobeniusRange
    (hR : ∀ r : R, algebraMap R k r ∈ (frobenius k p).fieldRange) :
    Ω[k⁄R] ≃ₗ[k] Ω[k⁄(frobenius k p).fieldRange] :=
  let d₁ : Derivation R k Ω[k⁄(frobenius k p).fieldRange] :=
    Derivation.mk'
      { toFun := fun x ↦ D (frobenius k p).fieldRange k x
        map_add' := fun x y ↦ map_add _ x y
        map_smul' := fun r x ↦ by
          rw [RingHom.id_apply, Algebra.smul_def, Derivation.leibniz,
            D_eq_zero_of_mem_fieldRange_frobenius (R := (frobenius k p).fieldRange) (hR r),
            smul_zero, add_zero, IsScalarTower.algebraMap_smul] }
      fun x y ↦ Derivation.leibniz _ x y
  let d₂ : Derivation (frobenius k p).fieldRange k Ω[k⁄R] :=
    Derivation.mk'
      { toFun := fun x ↦ D R k x
        map_add' := fun x y ↦ map_add _ x y
        map_smul' := fun c x ↦ by
          rw [RingHom.id_apply, Algebra.smul_def, Derivation.leibniz,
            D_eq_zero_of_mem_fieldRange_frobenius
              (x := algebraMap (frobenius k p).fieldRange k c) c.2,
            smul_zero, add_zero, IsScalarTower.algebraMap_smul] }
      fun x y ↦ Derivation.leibniz _ x y
  LinearEquiv.ofLinearMap d₁.liftKaehlerDifferential d₂.liftKaehlerDifferential
    (Derivation.liftKaehlerDifferential_unique _ _ (by
      ext x
      simp [d₁, d₂]))
    (Derivation.liftKaehlerDifferential_unique _ _ (by
      ext x
      simp [d₁, d₂]))

/-- `kaehlerEquivFrobeniusRange` sends `D R k x` to `D (frobenius k p).fieldRange k x`. -/
@[simp]
theorem kaehlerEquivFrobeniusRange_D
    (hR : ∀ r : R, algebraMap R k r ∈ (frobenius k p).fieldRange) (x : k) :
    kaehlerEquivFrobeniusRange p R k hR (D R k x) = D (frobenius k p).fieldRange k x := by
  simp [kaehlerEquivFrobeniusRange]

/-- The inverse of `kaehlerEquivFrobeniusRange` sends `D (frobenius k p).fieldRange k x` to
`D R k x`. -/
@[simp]
theorem kaehlerEquivFrobeniusRange_symm_D
    (hR : ∀ r : R, algebraMap R k r ∈ (frobenius k p).fieldRange) (x : k) :
    (kaehlerEquivFrobeniusRange p R k hR).symm (D (frobenius k p).fieldRange k x) = D R k x := by
  simp [kaehlerEquivFrobeniusRange]

end BaseRing

section CoordDerivation

variable {p : ℕ} [Fact p.Prime] {k : Type*} [Field k] [CharP k p] {ι : Type*}

private theorem neZero_of_prime : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩

attribute [local instance] neZero_of_prime

private def coordDerivationLinear {b : ι → k} (hb : IsPBasis p b) (j : ι) :
    k →ₗ[(frobenius k p).fieldRange] k :=
  hb.basis.constr (frobenius k p).fieldRange fun e ↦
    ((e j : ℕ) : k) * pMonomial p b (e - Finsupp.single j ⟨1, (Fact.out : p.Prime).one_lt⟩)

private theorem coordDerivationLinear_apply_pMonomial {b : ι → k} (hb : IsPBasis p b) (j : ι)
    (e : ι →₀ Fin p) :
    coordDerivationLinear hb j (pMonomial p b e) =
      ((e j : ℕ) : k) * pMonomial p b (e - Finsupp.single j ⟨1, (Fact.out : p.Prime).one_lt⟩) := by
  rw [← hb.basis_apply, coordDerivationLinear, hb.basis.constr_basis]

private theorem mul_coordDerivationLinear_pMonomial {b : ι → k} (hb : IsPBasis p b) (j : ι)
    (e : ι →₀ Fin p) :
    b j * coordDerivationLinear hb j (pMonomial p b e) = ((e j : ℕ) : k) * pMonomial p b e := by
  rw [coordDerivationLinear_apply_pMonomial]
  by_cases hj : e j = 0
  · simp [hj]
  · rw [mul_left_comm, mul_pMonomial_sub_single p (Fact.out : p.Prime).one_lt b e hj]

private theorem coordDerivationLinear_leibniz_pMonomial {b : ι → k} (hb : IsPBasis p b) (j : ι)
    (e e' : ι →₀ Fin p) :
    coordDerivationLinear hb j (pMonomial p b e * pMonomial p b e') =
      pMonomial p b e * coordDerivationLinear hb j (pMonomial p b e') +
        pMonomial p b e' * coordDerivationLinear hb j (pMonomial p b e) := by
  obtain ⟨c, hc⟩ := pMonomial_mul p b e e'
  have hsmul : coordDerivationLinear hb j (c ^ p * pMonomial p b (e + e')) =
      c ^ p * coordDerivationLinear hb j (pMonomial p b (e + e')) :=
    (coordDerivationLinear hb j).map_smul ⟨c ^ p, c, frobenius_def ..⟩ (pMonomial p b (e + e'))
  refine mul_left_cancel₀ (hb.isPIndependent.ne_zero j) ?_
  calc
    b j * coordDerivationLinear hb j (pMonomial p b e * pMonomial p b e')
        = c ^ p * (b j * coordDerivationLinear hb j (pMonomial p b (e + e'))) := by
          rw [hc, hsmul, mul_left_comm]
    _ = (((e + e') j : ℕ) : k) * (pMonomial p b e * pMonomial p b e') := by
          rw [mul_coordDerivationLinear_pMonomial, hc]; ring
    _ = (((e j : ℕ) : k) + ((e' j : ℕ) : k)) * (pMonomial p b e * pMonomial p b e') := by
          rw [Finsupp.add_apply, Fin.val_add, ← CharP.cast_eq_mod k p, Nat.cast_add]
    _ = b j * (pMonomial p b e * coordDerivationLinear hb j (pMonomial p b e') +
          pMonomial p b e' * coordDerivationLinear hb j (pMonomial p b e)) := by
          rw [mul_add, mul_left_comm (b j) (pMonomial p b e), mul_coordDerivationLinear_pMonomial,
            mul_left_comm (b j) (pMonomial p b e'), mul_coordDerivationLinear_pMonomial]
          ring

private theorem coordDerivationLinear_leibniz {b : ι → k} (hb : IsPBasis p b) (j : ι) (x y : k) :
    coordDerivationLinear hb j (x * y) =
      x * coordDerivationLinear hb j y + y * coordDerivationLinear hb j x := by
  let f := coordDerivationLinear hb j
  have hmon : ∀ (e : ι →₀ Fin p) (v : k),
      f (pMonomial p b e * v) = pMonomial p b e * f v + v * f (pMonomial p b e) := by
    intro e v
    let lhs : k →ₗ[(frobenius k p).fieldRange] k :=
      f.comp (LinearMap.mul (frobenius k p).fieldRange k (pMonomial p b e))
    let rhs : k →ₗ[(frobenius k p).fieldRange] k :=
      (LinearMap.mul (frobenius k p).fieldRange k (pMonomial p b e)).comp f +
        (LinearMap.mul (frobenius k p).fieldRange k).flip (f (pMonomial p b e))
    have heq : lhs = rhs := hb.basis.ext fun e' ↦ by
      simpa [lhs, rhs, f, mul_comm] using coordDerivationLinear_leibniz_pMonomial hb j e e'
    exact LinearMap.congr_fun heq v
  let lhs : k →ₗ[(frobenius k p).fieldRange] k :=
    f.comp (LinearMap.mul (frobenius k p).fieldRange k y)
  let rhs : k →ₗ[(frobenius k p).fieldRange] k :=
    LinearMap.mul (frobenius k p).fieldRange k (f y) +
      (LinearMap.mul (frobenius k p).fieldRange k y).comp f
  have heq : lhs = rhs := hb.basis.ext fun e ↦ by
    simpa [lhs, rhs, f, mul_comm] using hmon e y
  simpa [lhs, rhs, f, mul_comm] using LinearMap.congr_fun heq x

/-- The `j`-th coordinate `k ^ p`-derivation associated to a `p`-basis `b : ι → k`, sending each
`p`-monomial `∏ i, b i ^ (e i)` to `(e j : k) * ∏ i, b i ^ (e i - δ_{ij})`. -/
def IsPBasis.coordDerivation {b : ι → k} (hb : IsPBasis p b) (j : ι) :
    Derivation (frobenius k p).fieldRange k k :=
  Derivation.mk' (coordDerivationLinear hb j) (coordDerivationLinear_leibniz hb j)

/-- Evaluating `IsPBasis.coordDerivation` on a `p`-monomial decrements the `j`-th exponent and
multiplies by its original value. -/
theorem IsPBasis.coordDerivation_apply_pMonomial {b : ι → k} (hb : IsPBasis p b) (j : ι)
    (e : ι →₀ Fin p) :
    hb.coordDerivation j (pMonomial p b e) =
      ((e j : ℕ) : k) * pMonomial p b (e - Finsupp.single j ⟨1, (Fact.out : p.Prime).one_lt⟩) :=
  coordDerivationLinear_apply_pMonomial hb j e

/-- The `j`-th coordinate derivation maps `b j` to `1`. -/
@[simp]
theorem IsPBasis.coordDerivation_apply_self {b : ι → k} (hb : IsPBasis p b) (j : ι) :
    hb.coordDerivation j (b j) = 1 := by
  have h := hb.coordDerivation_apply_pMonomial j
    (Finsupp.single j ⟨1, (Fact.out : p.Prime).one_lt⟩)
  simpa using h

/-- The `j`-th coordinate derivation vanishes on `b i` for `i ≠ j`. -/
@[simp]
theorem IsPBasis.coordDerivation_apply_ne {b : ι → k} (hb : IsPBasis p b) {i j : ι}
    (hij : i ≠ j) : hb.coordDerivation j (b i) = 0 := by
  have h := hb.coordDerivation_apply_pMonomial j
    (Finsupp.single i ⟨1, (Fact.out : p.Prime).one_lt⟩)
  simpa [Finsupp.single_apply, hij] using h

end CoordDerivation

section KaehlerTheorems

variable {p : ℕ} [Fact p.Prime] {R k : Type*} [CommRing R] [Field k] [CharP k p] [Algebra R k]
variable {ι : Type*}

/-- The differentials `{D R k (b i)}` of a `p`-basis `b : ι → k` form a `k`-basis of `Ω[k⁄R]`,
for any base ring `R` whose image lies in `k ^ p`. -/
def IsPBasis.kaehlerBasis {b : ι → k} (hb : IsPBasis p b)
    (hR : ∀ r : R, algebraMap R k r ∈ (frobenius k p).fieldRange) :
    Module.Basis ι k Ω[k⁄R] :=
  have hlin : LinearIndependent k (fun i ↦ D R k (b i)) := by
    rw [linearIndependent_iff']
    intro s c hc j hj
    let φ : Ω[k⁄R] →ₗ[k] k :=
      (hb.coordDerivation j).liftKaehlerDifferential.comp
        (kaehlerEquivFrobeniusRange p R k hR).toLinearMap
    have hφ : ∀ i : ι, φ (D R k (b i)) = hb.coordDerivation j (b i) := fun i ↦ by
      simp [φ]
    have h0 := congrArg φ hc
    rw [map_sum, map_zero] at h0
    simp only [map_smul, hφ, smul_eq_mul] at h0
    rw [Finset.sum_eq_single j
      (fun i _ hij ↦ by rw [hb.coordDerivation_apply_ne hij, mul_zero])
      (fun h ↦ (h hj).elim), hb.coordDerivation_apply_self, mul_one] at h0
    exact h0
  have hspan : Submodule.span k (Set.range fun i ↦ D R k (b i)) = ⊤ := by
    rw [eq_top_iff, ← span_range_derivation R k, Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    refine D_mem_span_D_of_mem_adjoin b ?_
    rw [hb.adjoin_eq_top]
    exact IntermediateField.mem_top
  Module.Basis.mk hlin hspan.ge

/-- Evaluating `IsPBasis.kaehlerBasis` at `i` gives the differential `D R k (b i)`. -/
@[simp]
theorem IsPBasis.kaehlerBasis_apply {b : ι → k} (hb : IsPBasis p b)
    (hR : ∀ r : R, algebraMap R k r ∈ (frobenius k p).fieldRange) (i : ι) :
    hb.kaehlerBasis hR i = D R k (b i) := by
  rw [IsPBasis.kaehlerBasis, Module.Basis.coe_mk]

/-- A family in a field `k` of prime characteristic `p` is `p`-independent if and only if its
Kähler differentials over `R` are linearly independent over `k`, for any base ring `R` whose
image lies in `k ^ p`. -/
theorem isPIndependent_iff_linearIndependent_D
    (hR : ∀ r : R, algebraMap R k r ∈ (frobenius k p).fieldRange) (b : ι → k) :
    IsPIndependent p b ↔ LinearIndependent k (fun i ↦ D R k (b i)) := by
  constructor
  · intro hb
    let e : ι ≃ Set.range b := Equiv.ofBijective (fun i ↦ ⟨b i, i, rfl⟩)
      ⟨fun i j h ↦ hb.injective (congrArg Subtype.val h), fun ⟨_, i, hi⟩ ↦ ⟨i, Subtype.ext hi⟩⟩
    have hrange : IsPIndependent p ((↑) : Set.range b → k) := by
      have hcomp : (((↑) : Set.range b → k) ∘ e) = b := rfl
      exact (isPIndependent_equiv ((↑) : Set.range b → k) e).mp (hcomp.symm ▸ hb)
    obtain ⟨t, hsub, ht⟩ := exists_isPBasis_of_isPIndependent hrange
    let f : ι → t := fun i ↦ ⟨b i, hsub ⟨i, rfl⟩⟩
    have hf : Function.Injective f := fun i j h ↦ hb.injective (congrArg Subtype.val h)
    have hcoe : (fun i ↦ D R k (b i)) = (ht.kaehlerBasis hR) ∘ f :=
      funext fun i ↦ (ht.kaehlerBasis_apply hR (f i)).symm
    rw [hcoe]
    exact (ht.kaehlerBasis hR).linearIndependent.comp f hf
  · intro hlin
    by_contra hnot
    obtain ⟨i, hi⟩ := exists_mem_adjoin_erase_of_not_isPIndependent hnot
    have hbrange : Set.range (fun j : ({i}ᶜ : Set ι) ↦ b j) = b '' ({i}ᶜ : Set ι) := by
      ext y; simp
    have hmem := D_mem_span_D_of_mem_adjoin (R := R) (fun j : ({i}ᶜ : Set ι) ↦ b j)
      (hbrange.symm ▸ hi)
    have hrange : Set.range (fun j : ({i}ᶜ : Set ι) ↦ D R k (b j)) =
        (fun j ↦ D R k (b j)) '' ({i}ᶜ : Set ι) := by
      ext ω
      simp
    rw [hrange] at hmem
    exact hlin.notMem_span_image (Set.notMem_compl_iff.mpr rfl) hmem

/-- A family in a field `k` of prime characteristic `p` is a `p`-basis if and only if its
Kähler differentials over `R` are linearly independent and span `Ω[k⁄R]`, for any base ring `R`
whose image lies in `k ^ p`. -/
theorem isPBasis_iff_linearIndependent_and_span_D
    (hR : ∀ r : R, algebraMap R k r ∈ (frobenius k p).fieldRange) (b : ι → k) :
    IsPBasis p b ↔
      LinearIndependent k (fun i ↦ D R k (b i)) ∧
        Submodule.span k (Set.range fun i ↦ D R k (b i)) = ⊤ := by
  constructor
  · intro hb
    have hcoe : (fun i ↦ D R k (b i)) = ⇑(hb.kaehlerBasis hR) :=
      funext fun i ↦ (hb.kaehlerBasis_apply hR i).symm
    rw [hcoe]
    exact ⟨(hb.kaehlerBasis hR).linearIndependent, (hb.kaehlerBasis hR).span_eq⟩
  · rintro ⟨hlin, hspan⟩
    have hind : IsPIndependent p b := (isPIndependent_iff_linearIndependent_D hR b).mpr hlin
    refine (isPBasis_iff b).mpr ⟨hind, (span_range_pMonomial_eq_top_iff b).mpr ?_⟩
    rw [eq_top_iff]
    intro x _
    by_contra hx
    have hopt : IsPIndependent p (Option.elim' x b) := (isPIndependent_option_iff hind x).mpr hx
    have hopt_lin : LinearIndependent k (fun o ↦ D R k (Option.elim' x b o)) :=
      (isPIndependent_iff_linearIndependent_D hR _).mp hopt
    have hnotmem := hopt_lin.notMem_span_image (s := Set.range Option.some) (x := none) (by simp)
    have himg : (fun o ↦ D R k (Option.elim' x b o)) '' Set.range Option.some =
        Set.range (fun i ↦ D R k (b i)) := by
      ext ω
      simp
    rw [himg, hspan] at hnotmem
    exact hnotmem Submodule.mem_top

/-- In a field `k` of prime characteristic `p`, the kernel of the universal derivation
`D R k : k → Ω[k⁄R]` is the Frobenius subfield `k ^ p`, for any base ring `R` whose image lies in
`k ^ p`. -/
theorem D_eq_zero_iff_mem_fieldRange_frobenius
    (hR : ∀ r : R, algebraMap R k r ∈ (frobenius k p).fieldRange) (x : k) :
    D R k x = 0 ↔ x ∈ (frobenius k p).fieldRange := by
  refine ⟨fun hx ↦ ?_, D_eq_zero_of_mem_fieldRange_frobenius⟩
  by_contra hnot
  have hnot_adjoin :
      x ∉ IntermediateField.adjoin (frobenius k p).fieldRange
        (Set.range (Empty.elim : Empty → k)) := by
    rw [Set.range_eq_empty, IntermediateField.adjoin_empty, IntermediateField.mem_bot]
    rintro ⟨c, hc⟩
    exact hnot (hc ▸ c.2)
  have hopt : IsPIndependent p (Option.elim' x (Empty.elim : Empty → k)) :=
    (isPIndependent_option_iff (isPIndependent_empty _) x).mpr hnot_adjoin
  have hlin := (isPIndependent_iff_linearIndependent_D hR _).mp hopt
  exact hlin.ne_zero none (by simpa using hx)

/-- **Finiteness criterion for differentials**: without assuming `[k : k ^ p]` finite, `Ω[k⁄R]` is
finite-dimensional over `k` if and only if `k` is finite-dimensional over its Frobenius subfield
`k ^ p`, for any base ring `R` whose image lies in `k ^ p`. -/
theorem kaehler_finiteDimensional_iff (p : ℕ) [Fact p.Prime] (R k : Type*)
    [CommRing R] [Field k] [CharP k p] [Algebra R k]
    (hR : ∀ r : R, algebraMap R k r ∈ (frobenius k p).fieldRange) :
    FiniteDimensional k Ω[k⁄R] ↔ FiniteDimensional (frobenius k p).fieldRange k := by
  obtain ⟨t, ht⟩ := exists_isPBasis p k
  rw [← ht.finite_iff_finiteDimensional]
  constructor
  · intro hfd
    have : Fintype t := FiniteDimensional.fintypeBasisIndex (ht.kaehlerBasis hR)
    exact Finite.of_fintype t
  · intro hfin
    have : Fintype t := Fintype.ofFinite t
    exact Module.Finite.of_basis (ht.kaehlerBasis hR)

/-- **Degree-dimension formula**: when a field `k` of prime characteristic `p` is finite-dimensional
over its Frobenius subfield `k ^ p`, `[k : k ^ p] = p ^ dim_k Ω[k⁄R]` for any base ring `R` whose
image lies in `k ^ p`. -/
theorem finrank_fieldRange_frobenius_eq_pow_finrank_kaehler (p : ℕ) [Fact p.Prime] (R k : Type*)
    [CommRing R] [Field k] [CharP k p] [Algebra R k]
    (hR : ∀ r : R, algebraMap R k r ∈ (frobenius k p).fieldRange)
    [FiniteDimensional (frobenius k p).fieldRange k] :
    Module.finrank (frobenius k p).fieldRange k = p ^ Module.finrank k Ω[k⁄R] := by
  obtain ⟨t, ht⟩ := exists_isPBasis p k
  have hfin : Finite t := ht.finite_iff_finiteDimensional.mpr ‹_›
  have : Fintype t := Fintype.ofFinite t
  rw [ht.finrank_fieldRange_frobenius, Module.finrank_eq_card_basis (ht.kaehlerBasis hR)]

/-- A field `k` of prime characteristic `p` has vanishing Kähler differentials `Ω[k⁄R]` if and
only if `k` is perfect, for any base ring `R` whose image lies in `k ^ p`. -/
theorem subsingleton_kaehlerDifferential_iff_perfectRing (p : ℕ) [Fact p.Prime] (R k : Type*)
    [CommRing R] [Field k] [CharP k p] [Algebra R k]
    (hR : ∀ r : R, algebraMap R k r ∈ (frobenius k p).fieldRange) :
    Subsingleton Ω[k⁄R] ↔ PerfectRing k p := by
  constructor
  · intro _
    refine PerfectRing.ofSurjective k p fun x ↦ ?_
    exact (D_eq_zero_iff_mem_fieldRange_frobenius hR x).mp (Subsingleton.elim _ _)
  · intro hperf
    have hb : IsPBasis p (Empty.elim : Empty → k) :=
      (isPBasis_empty_iff_perfectRing _).mpr hperf
    exact (hb.kaehlerBasis hR).repr.toEquiv.subsingleton

end KaehlerTheorems

end TauCeti
