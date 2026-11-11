/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Homotopy
public import TauCeti.Algebra.Homology.HomologicalComplex.Basic
public import TauCeti.AlgebraicTopology.SimplicialSet.Homology.Coproduct
import Mathlib.Algebra.BigOperators.Intervals

/-!
# Chain retractions onto the chains of a simplicial subset

Let `i : L ⟶ K` be a monomorphism of simplicial sets and let `s` be a chain endomorphism of the
simplicial chains of `K`, with coefficients in `R`, together with a chain homotopy `h` from the
identity to `s`. Suppose that the homotopy operators `h` carry the chains of `L` into the chains
of `L` (then so does `s`), and that every simplex of `K` becomes a chain of `L` after finitely many
applications of `s`. Then the inclusion of the chains of `L` into the chains of `K` is a chain
homotopy equivalence, and even a deformation retract in the chain-level sense: it has a strict
retraction which is a homotopy inverse.

This is the abstract form of the small-chain theorem. There `s` is barycentric subdivision, `h` is
its prism operator, and `L` is the simplicial subset of simplices subordinate to an open cover;
every singular simplex becomes subordinate after enough subdivisions. Formulating it for an
arbitrary `i` lets the same argument run inside any subcomplex of singular chains that is stable
under subdivision, such as the smooth singular chains of a manifold.

The construction is Hatcher's. Iterating `h` gives chain homotopies from the identity to `sᵐ`
(`Homotopy.idPow`). Choosing for each simplex `σ` a number of iterations `chainRangeDepth` that
carries `σ` and all of its iterated faces into the chains of `L`, and using the corresponding
homotopy operator on the summand of `σ`, produces an operator `D` whose associated chain map
`ρ = 1 - ∂D - D∂` lands in the chains of `L` and restricts to the identity there.

## Main definitions and results

* `TauCeti.chainRange R i n`: the `n`-chains of `K` that factor through the chains of `L`.
* `TauCeti.chainRangeDepth`: a number of applications of `s`, monotone under passing to a face,
  which carries a simplex and all of its iterated faces into the chains of `L` when `s` preserves
  the chains of `L` and eventually carries every simplex into them.
* `TauCeti.chainRangeApprox i h`: the chain endomorphism `ρ`, chain homotopic to the identity
  (`TauCeti.chainRangeApproxHomotopy`), and equal to the identity on the chains of `L`
  (`TauCeti.chainComplexMap_comp_chainRangeApprox`).
* `TauCeti.mem_chainRange_ιChainComplex_comp_chainRangeApprox`: `ρ` lands in the chains of `L`.
* `TauCeti.chainRangeRetraction`: the resulting retraction onto the chains of `L`.
* `TauCeti.chainRangeHomotopyEquiv`: the inclusion of the chains of `L` is a chain homotopy
  equivalence.

## References

* A. Hatcher, *Algebraic Topology*, Section 2.1, proof of Proposition 2.21.
-/

public section

noncomputable section

open CategoryTheory Limits Simplicial

universe w v u

namespace TauCeti

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C] (R : C)
  {K L : SSet.{w}} (i : L ⟶ K)

/-- The subgroup of the simplicial `n`-chains of `K` with coefficients in `R` consisting of the
chains that factor through the chains of `L` along `i`. -/
def chainRange (n : ℕ) : AddSubgroup (R ⟶ (K.chainComplex R).X n) :=
  (Preadditive.rightComp R ((SSet.chainComplexMap i R).f n)).range

variable {R i}

lemma mem_chainRange_iff {n : ℕ} (f : R ⟶ (K.chainComplex R).X n) :
    f ∈ chainRange R i n ↔ ∃ g : R ⟶ (L.chainComplex R).X n,
      g ≫ (SSet.chainComplexMap i R).f n = f :=
  AddMonoidHom.mem_range

/-- The summand of the image of a simplex of `L` is a chain of `L`. -/
lemma ιChainComplex_app_mem_chainRange {n : ℕ} (σ : L _⦋n⦌) :
    K.ιChainComplex (i.app _ σ) ∈ chainRange R i n :=
  (mem_chainRange_iff _).2 ⟨L.ιChainComplex σ, by simp⟩

/-- A map of chain groups that restricts to the chains of `L` preserves the chains of `L`. -/
lemma comp_mem_chainRange {n m : ℕ} {f : R ⟶ (K.chainComplex R).X n}
    (hf : f ∈ chainRange R i n) {e : (K.chainComplex R).X n ⟶ (K.chainComplex R).X m}
    (he : ∃ g, g ≫ (SSet.chainComplexMap i R).f m = (SSet.chainComplexMap i R).f n ≫ e) :
    f ≫ e ∈ chainRange R i m := by
  obtain ⟨g, rfl⟩ := (mem_chainRange_iff _).1 hf
  obtain ⟨e', he'⟩ := he
  exact (mem_chainRange_iff _).2 ⟨g ≫ e', by rw [Category.assoc, he', Category.assoc]⟩

variable {s : K.chainComplex R ⟶ K.chainComplex R}

/-- Once a chain has been carried into the chains of `L` by `m` applications of an endomorphism
`s` preserving the chains of `L`, any larger number of applications keeps it there. -/
lemma comp_pow_mem_chainRange_of_le
    (hs : ∀ n, ∃ g, g ≫ (SSet.chainComplexMap i R).f n = (SSet.chainComplexMap i R).f n ≫ s.f n)
    {n m m' : ℕ} (hm : m ≤ m') {f : R ⟶ (K.chainComplex R).X n}
    (hf : f ≫ (End.of s ^ m).asHom.f n ∈ chainRange R i n) :
    f ≫ (End.of s ^ m').asHom.f n ∈ chainRange R i n := by
  induction m', hm using Nat.le_induction with
  | base => exact hf
  | succ m' _ ih =>
    rw [HomologicalComplex.pow_f_succ, ← Category.assoc]
    exact comp_mem_chainRange ih (hs n)

variable (i s)

/-- The least number of applications of `s` carrying the summand of a simplex of `K` into the
chains of `L`, if one exists, and `0` otherwise. -/
def chainRangeOrder {n : ℕ} (σ : K _⦋n⦌) : ℕ :=
  sInf {m | K.ιChainComplex σ ≫ (End.of s ^ m).asHom.f n ∈ chainRange R i n}

variable {i s}

/-- The order is at most any number of applications of `s` carrying the simplex into the chains of
`L`. -/
lemma chainRangeOrder_le {n m : ℕ} {σ : K _⦋n⦌}
    (hσ : K.ιChainComplex σ ≫ (End.of s ^ m).asHom.f n ∈ chainRange R i n) :
    chainRangeOrder i s σ ≤ m :=
  Nat.sInf_le hσ

/-- After `chainRangeOrder` applications of `s`, or any larger number, a simplex is a chain of
`L`, provided `s` preserves the chains of `L` and eventually carries every simplex into them. -/
theorem ιChainComplex_comp_pow_mem_chainRange
    (hs : ∀ n, ∃ g, g ≫ (SSet.chainComplexMap i R).f n = (SSet.chainComplexMap i R).f n ≫ s.f n)
    (hfin : ∀ n (σ : K _⦋n⦌), ∃ m, K.ιChainComplex σ ≫ (End.of s ^ m).asHom.f n ∈
      chainRange R i n)
    {n : ℕ} (σ : K _⦋n⦌) {m : ℕ} (hm : chainRangeOrder i s σ ≤ m) :
    K.ιChainComplex σ ≫ (End.of s ^ m).asHom.f n ∈ chainRange R i n :=
  comp_pow_mem_chainRange_of_le hs hm (Nat.sInf_mem (s := {m |
    K.ιChainComplex σ ≫ (End.of s ^ m).asHom.f n ∈ chainRange R i n}) (hfin n σ))

/-- A simplex of `L` needs no application of `s`. -/
@[simp]
lemma chainRangeOrder_app_eq_zero {n : ℕ} (σ : L _⦋n⦌) :
    chainRangeOrder i s (i.app _ σ) = 0 :=
  Nat.le_zero.1 (chainRangeOrder_le (by simpa using ιChainComplex_app_mem_chainRange σ))

variable (i s)

/-- The depth of a simplex of `K`: the maximum of `TauCeti.chainRangeOrder` over the simplex and
all of its iterated faces. When `s` preserves the chains of `L` and eventually carries every
simplex into them, the simplex and all of its iterated faces are chains of `L` after this many
applications of `s` (see `TauCeti.ιChainComplex_comp_pow_mem_chainRange`). Unlike
`TauCeti.chainRangeOrder`, it is monotone under passing to a face, which is what makes
`TauCeti.chainRangeApprox` below land in the chains of `L`. -/
def chainRangeDepth (n : ℕ) (σ : K _⦋n⦌) : ℕ :=
  match n, σ with
  | 0, σ => chainRangeOrder i s σ
  | n + 1, σ => max (chainRangeOrder i s σ)
      (Finset.univ.sup fun j : Fin (n + 2) ↦ chainRangeDepth n (K.δ j σ))

variable {i s}

lemma chainRangeOrder_le_chainRangeDepth (n : ℕ) (σ : K _⦋n⦌) :
    chainRangeOrder i s σ ≤ chainRangeDepth i s n σ := by
  cases n with
  | zero => exact le_rfl
  | succ n => exact le_max_left _ _

lemma chainRangeDepth_δ_le (n : ℕ) (σ : K _⦋n + 1⦌) (j : Fin (n + 2)) :
    chainRangeDepth i s n (K.δ j σ) ≤ chainRangeDepth i s (n + 1) σ := by
  rw [chainRangeDepth]
  exact le_max_of_le_right (Finset.le_sup (f := fun j : Fin (n + 2) ↦
    chainRangeDepth i s n (K.δ j σ)) (Finset.mem_univ j))

/-- A simplex of `L` has depth zero. -/
@[simp]
lemma chainRangeDepth_app_eq_zero : ∀ (n : ℕ) (σ : L _⦋n⦌),
    chainRangeDepth i s n (i.app _ σ) = 0 := by
  intro n
  induction n with
  | zero => exact fun σ ↦ chainRangeOrder_app_eq_zero σ
  | succ n ih =>
    intro σ
    rw [chainRangeDepth, chainRangeOrder_app_eq_zero, Nat.max_eq_right (Nat.zero_le _)]
    refine Nat.le_zero.1 (Finset.sup_le fun j _ ↦ ?_)
    -- The faces of the image of `σ` are the images of the faces of `σ`.
    have hδ : K.δ j (i.app _ σ) = i.app _ (L.δ j σ) :=
      (NatTrans.naturality_apply i (SimplexCategory.δ j).op σ).symm
    rw [hδ]
    exact (ih _).le

/-! ### The approximation -/

variable (i) (h : Homotopy (𝟙 (K.chainComplex R)) s)

/-- The chain-homotopy operator of the approximation. On the summand of a simplex `σ` it is the
operator of the iterated homotopy `h.idPow` from the identity to `sᵐ`, where `m` is the depth of
`σ`. -/
def chainRangeApproxHom (a b : ℕ) : (K.chainComplex R).X a ⟶ (K.chainComplex R).X b :=
  Cofan.IsColimit.desc (K.isColimitChainComplexXCofan R a) fun σ ↦
    K.ιChainComplex σ ≫ (h.idPow (chainRangeDepth i s a σ)).hom a b

@[reassoc (attr := simp)]
lemma ιChainComplex_chainRangeApproxHom {a b : ℕ} (σ : K _⦋a⦌) :
    K.ιChainComplex σ ≫ chainRangeApproxHom i h a b =
      K.ιChainComplex σ ≫ (h.idPow (chainRangeDepth i s a σ)).hom a b :=
  Cofan.IsColimit.fac _ _ σ

lemma chainRangeApproxHom_eq_zero (a b : ℕ) (hab : ¬ (ComplexShape.down ℕ).Rel b a) :
    chainRangeApproxHom i h a b = 0 := by
  ext σ
  rw [ιChainComplex_chainRangeApproxHom, (h.idPow (chainRangeDepth i s a σ)).zero a b hab]

/-- The approximation: a chain endomorphism of the chains of `K`, chain homotopic to the identity,
all of whose values are chains of `L` under the hypotheses of
`TauCeti.mem_chainRange_ιChainComplex_comp_chainRangeApprox`. It is Hatcher's operator
`ρ = 1 - ∂D - D∂`, where `D` is `TauCeti.chainRangeApproxHom`. -/
def chainRangeApprox : K.chainComplex R ⟶ K.chainComplex R :=
  𝟙 _ - Homotopy.nullHomotopicMap (chainRangeApproxHom i h)

lemma chainRangeApprox_f (n : ℕ) :
    (chainRangeApprox i h).f n = 𝟙 _ -
      (dNext n (chainRangeApproxHom i h) + prevD n (chainRangeApproxHom i h)) := by
  rw [chainRangeApprox, HomologicalComplex.sub_f_apply, HomologicalComplex.id_f,
    (Homotopy.nullHomotopy _ (chainRangeApproxHom_eq_zero i h)).comm n]
  simp [Homotopy.nullHomotopy]

/-- The approximation is chain homotopic to the identity. -/
def chainRangeApproxHomotopy : Homotopy (𝟙 _) (chainRangeApprox i h) where
  hom := chainRangeApproxHom i h
  zero := chainRangeApproxHom_eq_zero i h
  comm n := by
    rw [chainRangeApprox_f]
    abel

/-- The approximation operator kills the chains of `L`. -/
lemma chainComplexMap_f_comp_chainRangeApproxHom (a b : ℕ) :
    (SSet.chainComplexMap i R).f a ≫ chainRangeApproxHom i h a b = 0 := by
  ext τ
  rw [← Category.assoc, SSet.ι_chainComplexMap_f, ιChainComplex_chainRangeApproxHom,
    chainRangeDepth_app_eq_zero]
  simp [Homotopy.idPow_hom]

/-- The approximation restricts to the identity on the chains of `L`. -/
@[reassoc (attr := simp)]
lemma chainComplexMap_comp_chainRangeApprox :
    SSet.chainComplexMap i R ≫ chainRangeApprox i h = SSet.chainComplexMap i R := by
  ext n : 1
  have hd : (SSet.chainComplexMap i R).f n ≫ dNext n (chainRangeApproxHom i h) = 0 := by
    rw [dNext, AddMonoidHom.mk'_apply, ← Category.assoc, HomologicalComplex.Hom.comm,
      Category.assoc, chainComplexMap_f_comp_chainRangeApproxHom, comp_zero]
  have hp : (SSet.chainComplexMap i R).f n ≫ prevD n (chainRangeApproxHom i h) = 0 := by
    rw [prevD, AddMonoidHom.mk'_apply, ← Category.assoc,
      chainComplexMap_f_comp_chainRangeApproxHom, zero_comp]
  rw [HomologicalComplex.comp_f, chainRangeApprox_f, Preadditive.comp_sub, Category.comp_id,
    Preadditive.comp_add, hd, hp, add_zero, sub_zero]

variable {i h}
variable
  (hh : ∀ n, ∃ g, g ≫ (SSet.chainComplexMap i R).f (n + 1) =
    (SSet.chainComplexMap i R).f n ≫ h.hom n (n + 1))

variable
  (hfin : ∀ n (σ : K _⦋n⦌), ∃ m, K.ιChainComplex σ ≫ (End.of s ^ m).asHom.f n ∈
    chainRange R i n)

include hh hfin

/-- Enlarging the number of iterations in the iterated homotopy operator changes it by a chain of
`L`, provided the simplex is already a chain of `L` after the smaller number of applications of
`s`. -/
lemma ιChainComplex_comp_idPow_hom_sub_mem_chainRange {n : ℕ} (σ : K _⦋n⦌) {m m' : ℕ}
    (hm' : chainRangeOrder i s σ ≤ m') (hmm : m' ≤ m) :
    K.ιChainComplex σ ≫ ((h.idPow m).hom n (n + 1) - (h.idPow m').hom n (n + 1)) ∈
      chainRange R i (n + 1) := by
  have hsum : (h.idPow m).hom n (n + 1) - (h.idPow m').hom n (n + 1) =
      ∑ k ∈ Finset.Ico m' m, (End.of s ^ k).asHom.f n ≫ h.hom n (n + 1) := by
    rw [Homotopy.idPow_hom, Homotopy.idPow_hom, Finset.sum_Ico_eq_sub _ hmm]
  rw [hsum, Preadditive.comp_sum]
  refine AddSubgroup.sum_mem _ fun k hk ↦ ?_
  rw [← Category.assoc]
  exact comp_mem_chainRange (ιChainComplex_comp_pow_mem_chainRange
    (h.exists_comp_f_eq_comp_f _ _ (fun _ ↦ ⟨𝟙 _, by simp⟩) fun n _ hn ↦ hn ▸ hh n) hfin σ
    (hm'.trans (Finset.mem_Ico.1 hk).1)) (hh n)

/-- **The approximation lands in the chains of `L`.** -/
theorem mem_chainRange_ιChainComplex_comp_chainRangeApprox {n : ℕ} (σ : K _⦋n⦌) :
    K.ιChainComplex σ ≫ (chainRangeApprox i h).f n ∈ chainRange R i n := by
  set m := chainRangeDepth i s n σ
  -- The two homotopy operators agree on the summand of `σ` in the `prevD` direction.
  have hprev : K.ιChainComplex σ ≫
      (prevD n (h.idPow m).hom - prevD n (chainRangeApproxHom i h)) = 0 := by
    rw [Preadditive.comp_sub, Homotopy.prevD_chainComplex, Homotopy.prevD_chainComplex,
      ← Category.assoc, ← Category.assoc, ιChainComplex_chainRangeApproxHom, sub_self]
  -- In the `dNext` direction they differ by a chain of `L`, because the depth of a face of `σ`
  -- is at most the depth of `σ`.
  have hdnext : K.ιChainComplex σ ≫
      (dNext n (h.idPow m).hom - dNext n (chainRangeApproxHom i h)) ∈ chainRange R i n := by
    cases n with
    | zero => simp
    | succ k =>
      rw [Preadditive.comp_sub, Homotopy.dNext_succ_chainComplex,
        Homotopy.dNext_succ_chainComplex, ← Category.assoc, ← Category.assoc,
        SSet.ιChainComplex_d, Preadditive.sum_comp, Preadditive.sum_comp,
        ← Finset.sum_sub_distrib]
      refine AddSubgroup.sum_mem _ fun j _ ↦ ?_
      rw [Preadditive.zsmul_comp, Preadditive.zsmul_comp, ← smul_sub, ← Preadditive.comp_sub,
        Preadditive.comp_sub, ιChainComplex_chainRangeApproxHom, ← Preadditive.comp_sub]
      exact AddSubgroup.zsmul_mem _
        (ιChainComplex_comp_idPow_hom_sub_mem_chainRange hh hfin _
          (chainRangeOrder_le_chainRangeDepth k _) (chainRangeDepth_δ_le k σ j)) _
  have hf : K.ιChainComplex σ ≫ (chainRangeApprox i h).f n =
      K.ιChainComplex σ ≫ (End.of s ^ m).asHom.f n +
        K.ιChainComplex σ ≫ (dNext n (h.idPow m).hom - dNext n (chainRangeApproxHom i h)) := by
    have hsplit : (chainRangeApprox i h).f n =
        (End.of s ^ m).asHom.f n +
          (dNext n (h.idPow m).hom - dNext n (chainRangeApproxHom i h)) +
          (prevD n (h.idPow m).hom - prevD n (chainRangeApproxHom i h)) := by
      rw [chainRangeApprox_f, ← HomologicalComplex.id_f, (h.idPow m).comm n]
      abel
    rw [hsplit, Preadditive.comp_add, Preadditive.comp_add, hprev, add_zero]
  rw [hf]
  exact AddSubgroup.add_mem _ (ιChainComplex_comp_pow_mem_chainRange
    (h.exists_comp_f_eq_comp_f _ _ (fun _ ↦ ⟨𝟙 _, by simp⟩) fun n _ hn ↦ hn ▸ hh n) hfin σ
    (chainRangeOrder_le_chainRangeDepth n σ)) hdnext

/-! ### The retraction onto the chains of `L` -/

private theorem exists_comp_eq_ιChainComplex_comp_chainRangeApprox {n : ℕ} (σ : K _⦋n⦌) :
    ∃ g : R ⟶ (L.chainComplex R).X n,
      g ≫ (SSet.chainComplexMap i R).f n = K.ιChainComplex σ ≫ (chainRangeApprox i h).f n :=
  (mem_chainRange_iff _).1 (mem_chainRange_ιChainComplex_comp_chainRangeApprox hh hfin σ)

/-- The degreewise factorisation of the approximation through the chains of `L`, obtained by
choosing a factorisation on each summand. -/
private def chainRangeRetractionX (n : ℕ) : (K.chainComplex R).X n ⟶ (L.chainComplex R).X n :=
  Cofan.IsColimit.desc (K.isColimitChainComplexXCofan R n) fun σ ↦
    (exists_comp_eq_ιChainComplex_comp_chainRangeApprox hh hfin σ).choose

private lemma ιChainComplex_chainRangeRetractionX {n : ℕ} (σ : K _⦋n⦌) :
    K.ιChainComplex σ ≫ chainRangeRetractionX hh hfin n =
      (exists_comp_eq_ιChainComplex_comp_chainRangeApprox hh hfin σ).choose :=
  Cofan.IsColimit.fac _ _ σ

@[reassoc (attr := simp)]
private lemma chainRangeRetractionX_comp (n : ℕ) :
    chainRangeRetractionX hh hfin n ≫ (SSet.chainComplexMap i R).f n =
      (chainRangeApprox i h).f n := by
  ext σ
  rw [← Category.assoc, ιChainComplex_chainRangeRetractionX]
  exact (exists_comp_eq_ιChainComplex_comp_chainRangeApprox hh hfin σ).choose_spec

variable [Mono i]

/-- **The retraction of the chains of `K` onto the chains of `L`.** It is the approximation
`TauCeti.chainRangeApprox`, factored through the chains of `L`. -/
def chainRangeRetraction : K.chainComplex R ⟶ L.chainComplex R where
  f := chainRangeRetractionX hh hfin
  comm' a b _ := by
    apply (cancel_mono ((SSet.chainComplexMap i R).f b)).1
    rw [Category.assoc, ← HomologicalComplex.Hom.comm, ← Category.assoc,
      chainRangeRetractionX_comp, Category.assoc, chainRangeRetractionX_comp,
      HomologicalComplex.Hom.comm]

@[reassoc (attr := simp)]
lemma chainRangeRetraction_comp_chainComplexMap :
    chainRangeRetraction hh hfin ≫ SSet.chainComplexMap i R = chainRangeApprox i h := by
  ext n : 1
  exact chainRangeRetractionX_comp hh hfin n

@[reassoc (attr := simp)]
lemma chainComplexMap_comp_chainRangeRetraction :
    SSet.chainComplexMap i R ≫ chainRangeRetraction hh hfin = 𝟙 _ := by
  apply (cancel_mono (SSet.chainComplexMap i R)).1
  rw [Category.assoc, chainRangeRetraction_comp_chainComplexMap,
    chainComplexMap_comp_chainRangeApprox, Category.id_comp]

/-- **The chains of `L` are a deformation retract of the chains of `K`.** If a chain endomorphism
`s` of the chains of `K` is chain homotopic to the identity through a homotopy `h`, the operators
of `h` restrict to the chains of `L`, and every simplex of `K` is carried into the
chains of `L` by some power of `s`, then the inclusion of the chains of `L` is a chain homotopy
equivalence. Its homotopy inverse `TauCeti.chainRangeRetraction` is a strict retraction. -/
def chainRangeHomotopyEquiv : HomotopyEquiv (L.chainComplex R) (K.chainComplex R) where
  hom := SSet.chainComplexMap i R
  inv := chainRangeRetraction hh hfin
  homotopyHomInvId := Homotopy.ofEq (chainComplexMap_comp_chainRangeRetraction hh hfin)
  homotopyInvHomId := (Homotopy.ofEq (chainRangeRetraction_comp_chainComplexMap hh hfin)).trans
    (chainRangeApproxHomotopy i h).symm

@[simp]
lemma chainRangeHomotopyEquiv_hom :
    (chainRangeHomotopyEquiv hh hfin).hom = SSet.chainComplexMap i R := (rfl)

@[simp]
lemma chainRangeHomotopyEquiv_inv :
    (chainRangeHomotopyEquiv hh hfin).inv = chainRangeRetraction hh hfin := (rfl)

end TauCeti
