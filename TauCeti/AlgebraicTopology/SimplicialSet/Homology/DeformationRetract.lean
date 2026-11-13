/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.CategoryTheory.Endomorphism
public import TauCeti.Algebra.Homology.Homotopy
public import TauCeti.AlgebraicTopology.SimplicialSet.Homology.Coproduct

/-!
# Chains of a simplicial subset as a deformation retract, by iterated subdivision

Let `i : L ⟶ K` be a monomorphism of simplicial sets, `s` a chain endomorphism of the chains of
`K`, and `h` a chain homotopy from the identity to `s`.  Suppose that `s` and the components of `h`
preserve the chains of `L`, and that every simplex of `K` becomes a chain of `L` after finitely
many applications of `s`.  Then the inclusion of the chains of `L` into the chains of `K` is a
deformation retract in the chain-level sense: it has a strict retraction which is a homotopy
inverse (`TauCeti.chainComplexMapHomotopyEquivOfSubdivision`).

The construction is Hatcher's proof of the small-chain theorem, with `s` an abstract subdivision
operator.  The `m`-fold power `sᵐ` is chain homotopic to the identity through
`∑_{k < m} sᵏ ≫ h`.  Taking for each simplex `σ` of `K` a number `TauCeti.subdivisionDepth` of
iterations that works simultaneously for `σ` and all of its iterated faces produces a
chain-homotopy operator `D` whose associated map `ρ = 1 - ∂D - D∂` is a chain map landing in the
chains of `L`.  Since `D` vanishes on simplices of `L`, `ρ` restricts to the identity there.

The main instance is barycentric subdivision of singular chains, with `L` the simplices subordinate
to an open cover (`TauCeti.smallSingularChainHomotopyEquiv`), and its restriction to affinely
stable subcomplexes of the singular simplicial set (`TauCeti.subcomplexSmallChainHomotopyEquiv`).

## Main definitions and results

* `TauCeti.chainRange R i n`: the subgroup of the `n`-chains of `K` factoring through the chains
  of `L`.
* `TauCeti.subdivisionDepth`: a number of iterations of `s` making a simplex and all of its
  iterated faces chains of `L`, monotone under passing to a face.
* `TauCeti.subdivisionApprox`: the chain endomorphism `ρ`, with
  `TauCeti.subdivisionApproxHomotopy` the chain homotopy to the identity and
  `TauCeti.ιChainComplex_comp_subdivisionApprox_mem_chainRange` the statement that it lands in
  the chains of `L`.
* `TauCeti.subdivisionRetraction`: the resulting retraction of the chains of `K` onto those of
  `L`.
* `TauCeti.chainComplexMapHomotopyEquivOfSubdivision`: the inclusion of the chains of `L` is a
  chain homotopy equivalence.

## References

* A. Hatcher, *Algebraic Topology*, Section 2.1, Proposition 2.21.
-/

public section

noncomputable section

open CategoryTheory Limits Simplicial

universe w v u

namespace TauCeti

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C] (R : C)
  {K L : SSet.{w}} (i : L ⟶ K)

/-- The subgroup of the `n`-chains of `K` with coefficients in `R` consisting of the chains that
factor through the chains of `L` along the monomorphism `i : L ⟶ K`. -/
def chainRange (n : ℕ) : AddSubgroup (R ⟶ (K.chainComplex R).X n) :=
  (Preadditive.rightComp R ((SSet.chainComplexMap i R).f n)).range

variable {R i}

lemma mem_chainRange_iff {n : ℕ} (f : R ⟶ (K.chainComplex R).X n) :
    f ∈ chainRange R i n ↔
      ∃ g : R ⟶ (L.chainComplex R).X n, g ≫ (SSet.chainComplexMap i R).f n = f :=
  AddMonoidHom.mem_range

/-- The summand of a simplex in the image of `i` is a chain of `L`. -/
lemma ιChainComplex_app_mem_chainRange {n : ℕ} (τ : L _⦋n⦌) :
    K.ιChainComplex (i.app _ τ) ∈ chainRange R i n :=
  (mem_chainRange_iff _).2 ⟨L.ιChainComplex τ, by simp⟩

variable {s : K.chainComplex R ⟶ K.chainComplex R}

/-- Once a chain has become a chain of `L` after `m` iterations of an operator preserving the
chains of `L`, it stays one after any larger number of iterations. -/
lemma comp_pow_f_mem_chainRange_of_le
    (hs : ∀ n, ∀ f ∈ chainRange R i n, f ≫ s.f n ∈ chainRange R i n) {n m m' : ℕ} (hm : m ≤ m')
    {f : R ⟶ (K.chainComplex R).X n}
    (hf : f ≫ (End.of s ^ m).asHom.f n ∈ chainRange R i n) :
    f ≫ (End.of s ^ m').asHom.f n ∈ chainRange R i n := by
  induction m', hm using Nat.le_induction with
  | base => exact hf
  | succ m' _ ih =>
    rw [HomologicalComplex.pow_f_succ, ← Category.assoc]
    exact hs n _ ih

variable (R i s)

/-- The least number of iterations of `s` after which a simplex of `K` becomes a chain of `L`. -/
def subdivisionOrder {n : ℕ} (σ : K _⦋n⦌) : ℕ :=
  sInf {m | K.ιChainComplex σ ≫ (End.of s ^ m).asHom.f n ∈ chainRange R i n}

/-- The subdivision order is at most any number of iterations that makes the simplex a chain
of `L`. -/
lemma subdivisionOrder_le {n m : ℕ} {σ : K _⦋n⦌}
    (hσ : K.ιChainComplex σ ≫ (End.of s ^ m).asHom.f n ∈ chainRange R i n) :
    subdivisionOrder R i s σ ≤ m :=
  Nat.sInf_le hσ

/-- After `subdivisionOrder` iterations, or any larger number, a simplex of `K` is a chain of `L`,
provided some number of iterations makes it one. -/
theorem ιChainComplex_comp_pow_f_mem_chainRange
    (hs : ∀ n, ∀ f ∈ chainRange R i n, f ≫ s.f n ∈ chainRange R i n)
    (hfin : ∀ n (σ : K _⦋n⦌), ∃ m, K.ιChainComplex σ ≫ (End.of s ^ m).asHom.f n ∈
      chainRange R i n)
    {n : ℕ} (σ : K _⦋n⦌) {m : ℕ} (hm : subdivisionOrder R i s σ ≤ m) :
    K.ιChainComplex σ ≫ (End.of s ^ m).asHom.f n ∈ chainRange R i n :=
  comp_pow_f_mem_chainRange_of_le hs hm
    (Nat.sInf_mem (s := {m | K.ιChainComplex σ ≫ (End.of s ^ m).asHom.f n ∈ chainRange R i n})
      (hfin n σ))

/-- A simplex in the image of `i` needs no iteration. -/
@[simp]
lemma subdivisionOrder_app_eq_zero {n : ℕ} (τ : L _⦋n⦌) :
    subdivisionOrder R i s (i.app _ τ) = 0 :=
  Nat.le_zero.1 (Nat.sInf_le (by simpa using ιChainComplex_app_mem_chainRange (R := R) (i := i) τ))

/-- The subdivision depth of a simplex of `K`: a number of iterations of `s` after which the
simplex and all of its iterated faces are chains of `L`.  Unlike the order, it is monotone under
passing to a face, which is what makes the operator `TauCeti.subdivisionApproxHom` below land in
the chains of `L`. -/
def subdivisionDepth (n : ℕ) (σ : K _⦋n⦌) : ℕ :=
  match n, σ with
  | 0, σ => subdivisionOrder R i s σ
  | n + 1, σ => max (subdivisionOrder R i s σ)
      (Finset.univ.sup fun j : Fin (n + 2) ↦ subdivisionDepth n (K.δ j σ))

lemma subdivisionOrder_le_subdivisionDepth (n : ℕ) (σ : K _⦋n⦌) :
    subdivisionOrder R i s σ ≤ subdivisionDepth R i s n σ := by
  cases n with
  | zero => exact le_rfl
  | succ n => exact le_max_left _ _

lemma subdivisionDepth_δ_le (n : ℕ) (σ : K _⦋n + 1⦌) (j : Fin (n + 2)) :
    subdivisionDepth R i s n (K.δ j σ) ≤ subdivisionDepth R i s (n + 1) σ := by
  rw [subdivisionDepth]
  exact le_max_of_le_right (Finset.le_sup (f := fun j : Fin (n + 2) ↦
    subdivisionDepth R i s n (K.δ j σ)) (Finset.mem_univ j))

@[simp]
lemma subdivisionDepth_app_eq_zero : ∀ (n : ℕ) (τ : L _⦋n⦌),
    subdivisionDepth R i s n (i.app _ τ) = 0 := by
  intro n
  induction n with
  | zero => exact fun τ ↦ subdivisionOrder_app_eq_zero R i s τ
  | succ n ih =>
    intro τ
    rw [subdivisionDepth, subdivisionOrder_app_eq_zero, Nat.max_eq_right (Nat.zero_le _)]
    exact Nat.le_zero.1 (Finset.sup_le fun j _ ↦ by rw [← SSet.δ_naturality_apply, ih])

/-! ### The approximation -/

variable {s} (h : Homotopy (𝟙 _) s)

/-- The chain-homotopy operator of the approximation.  On the summand of a simplex `σ` it is the
iterated operator of the chain homotopy from the identity to the `subdivisionDepth`-fold power of
`s`. -/
def subdivisionApproxHom (a b : ℕ) : (K.chainComplex R).X a ⟶ (K.chainComplex R).X b :=
  Cofan.IsColimit.desc (K.isColimitChainComplexXCofan R a) fun σ ↦
    K.ιChainComplex σ ≫ (h.idPow (subdivisionDepth R i s a σ)).hom a b

@[reassoc (attr := simp)]
lemma ιChainComplex_subdivisionApproxHom {a b : ℕ} (σ : K _⦋a⦌) :
    K.ιChainComplex σ ≫ subdivisionApproxHom R i h a b =
      K.ιChainComplex σ ≫ (h.idPow (subdivisionDepth R i s a σ)).hom a b :=
  Cofan.IsColimit.fac _ _ σ

lemma subdivisionApproxHom_eq_zero (a b : ℕ) (hab : ¬ (ComplexShape.down ℕ).Rel b a) :
    subdivisionApproxHom R i h a b = 0 := by
  ext σ
  rw [ιChainComplex_subdivisionApproxHom, (h.idPow (subdivisionDepth R i s a σ)).zero a b hab]

/-- The approximation of the chains of `K` by chains of `L`: a chain endomorphism homotopic to the
identity, which under the hypotheses of
`TauCeti.ιChainComplex_comp_subdivisionApprox_mem_chainRange` takes values in the chains of `L`.
It is Hatcher's operator `ρ = 1 - ∂D - D∂`, where `D` is `TauCeti.subdivisionApproxHom`. -/
def subdivisionApprox : K.chainComplex R ⟶ K.chainComplex R :=
  𝟙 _ - Homotopy.nullHomotopicMap (subdivisionApproxHom R i h)

lemma subdivisionApprox_f (n : ℕ) :
    (subdivisionApprox R i h).f n = 𝟙 _ -
      (dNext n (subdivisionApproxHom R i h) + prevD n (subdivisionApproxHom R i h)) := by
  rw [subdivisionApprox, HomologicalComplex.sub_f_apply, HomologicalComplex.id_f,
    (Homotopy.nullHomotopy _ (subdivisionApproxHom_eq_zero R i h)).comm n]
  simp [Homotopy.nullHomotopy]

/-- The approximation is chain homotopic to the identity. -/
def subdivisionApproxHomotopy : Homotopy (𝟙 _) (subdivisionApprox R i h) where
  hom := subdivisionApproxHom R i h
  zero := subdivisionApproxHom_eq_zero R i h
  comm n := by
    rw [subdivisionApprox_f]
    abel

/-- The approximation operator kills the chains of `L`. -/
lemma chainComplexMap_f_comp_subdivisionApproxHom (a b : ℕ) :
    (SSet.chainComplexMap i R).f a ≫ subdivisionApproxHom R i h a b = 0 := by
  ext τ
  rw [← Category.assoc, SSet.ι_chainComplexMap_f]
  simp

/-- The approximation restricts to the identity on the chains of `L`. -/
@[reassoc (attr := simp)]
lemma chainComplexMap_comp_subdivisionApprox :
    SSet.chainComplexMap i R ≫ subdivisionApprox R i h = SSet.chainComplexMap i R := by
  ext n : 1
  have hd : (SSet.chainComplexMap i R).f n ≫ dNext n (subdivisionApproxHom R i h) = 0 := by
    rw [dNext, AddMonoidHom.mk'_apply, ← Category.assoc, HomologicalComplex.Hom.comm,
      Category.assoc, chainComplexMap_f_comp_subdivisionApproxHom, comp_zero]
  have hp : (SSet.chainComplexMap i R).f n ≫ prevD n (subdivisionApproxHom R i h) = 0 := by
    rw [prevD, AddMonoidHom.mk'_apply, ← Category.assoc,
      chainComplexMap_f_comp_subdivisionApproxHom, zero_comp]
  rw [HomologicalComplex.comp_f, subdivisionApprox_f, Preadditive.comp_sub, Category.comp_id,
    Preadditive.comp_add, hd, hp, add_zero, sub_zero]

variable {R i h}
variable (hs : ∀ n, ∀ f ∈ chainRange R i n, f ≫ s.f n ∈ chainRange R i n)
  (hh : ∀ n, ∀ f ∈ chainRange R i n, f ≫ h.hom n (n + 1) ∈ chainRange R i (n + 1))
  (hfin : ∀ n (σ : K _⦋n⦌), ∃ m, K.ιChainComplex σ ≫ (End.of s ^ m).asHom.f n ∈
    chainRange R i n)

include hs hh hfin

/-- Enlarging the number of iterations in the iterated homotopy operator changes it by a chain of
`L`, provided the simplex is already a chain of `L` after the smaller number. -/
lemma ιChainComplex_comp_idPow_hom_sub_mem_chainRange {n : ℕ} (σ : K _⦋n⦌) {m m' : ℕ}
    (hm' : subdivisionOrder R i s σ ≤ m') (hmm : m' ≤ m) :
    K.ιChainComplex σ ≫ ((h.idPow m).hom n (n + 1) - (h.idPow m').hom n (n + 1)) ∈
      chainRange R i (n + 1) := by
  have hsum : (h.idPow m).hom n (n + 1) - (h.idPow m').hom n (n + 1) =
      ∑ k ∈ Finset.Ico m' m, (End.of s ^ k).asHom.f n ≫ h.hom n (n + 1) := by
    rw [Homotopy.idPow_hom, Homotopy.idPow_hom, Finset.sum_Ico_eq_sub _ hmm]
  rw [hsum, Preadditive.comp_sum]
  refine AddSubgroup.sum_mem _ fun k hk ↦ ?_
  rw [← Category.assoc]
  exact hh n _ (ιChainComplex_comp_pow_f_mem_chainRange R i s hs hfin σ
    (hm'.trans (Finset.mem_Ico.1 hk).1))

/-- **The approximation lands in the chains of `L`.** -/
theorem ιChainComplex_comp_subdivisionApprox_mem_chainRange {n : ℕ} (σ : K _⦋n⦌) :
    K.ιChainComplex σ ≫ (subdivisionApprox R i h).f n ∈ chainRange R i n := by
  set m := subdivisionDepth R i s n σ
  -- The two homotopy operators agree on the summand of `σ` in the `prevD` direction.
  have hprev : K.ιChainComplex σ ≫
      (prevD n (h.idPow m).hom - prevD n (subdivisionApproxHom R i h)) = 0 := by
    rw [Preadditive.comp_sub, Homotopy.prevD_chainComplex, Homotopy.prevD_chainComplex,
      ← Category.assoc, ← Category.assoc, ιChainComplex_subdivisionApproxHom, sub_self]
  -- In the `dNext` direction they differ by a chain of `L`, because the depth of a face of `σ` is
  -- at most the depth of `σ`.
  have hdnext : K.ιChainComplex σ ≫
      (dNext n (h.idPow m).hom - dNext n (subdivisionApproxHom R i h)) ∈ chainRange R i n := by
    cases n with
    | zero => simp
    | succ k =>
      rw [Preadditive.comp_sub, Homotopy.dNext_succ_chainComplex,
        Homotopy.dNext_succ_chainComplex, ← Category.assoc, ← Category.assoc,
        SSet.ιChainComplex_d, Preadditive.sum_comp, Preadditive.sum_comp,
        ← Finset.sum_sub_distrib]
      refine AddSubgroup.sum_mem _ fun j _ ↦ ?_
      rw [Preadditive.zsmul_comp, Preadditive.zsmul_comp, ← smul_sub, ← Preadditive.comp_sub,
        Preadditive.comp_sub, ιChainComplex_subdivisionApproxHom, ← Preadditive.comp_sub]
      exact AddSubgroup.zsmul_mem _
        (ιChainComplex_comp_idPow_hom_sub_mem_chainRange hs hh hfin _
          (subdivisionOrder_le_subdivisionDepth R i s k _)
          (subdivisionDepth_δ_le R i s k σ j)) _
  have hf : K.ιChainComplex σ ≫ (subdivisionApprox R i h).f n =
      K.ιChainComplex σ ≫ (End.of s ^ m).asHom.f n +
        K.ιChainComplex σ ≫
          (dNext n (h.idPow m).hom - dNext n (subdivisionApproxHom R i h)) := by
    have hsplit : (subdivisionApprox R i h).f n =
        (End.of s ^ m).asHom.f n +
          (dNext n (h.idPow m).hom - dNext n (subdivisionApproxHom R i h)) +
          (prevD n (h.idPow m).hom - prevD n (subdivisionApproxHom R i h)) := by
      rw [subdivisionApprox_f, ← HomologicalComplex.id_f, (h.idPow m).comm n]
      abel
    rw [hsplit, Preadditive.comp_add, Preadditive.comp_add, hprev, add_zero]
  rw [hf]
  exact AddSubgroup.add_mem _ (ιChainComplex_comp_pow_f_mem_chainRange R i s hs hfin σ
    (subdivisionOrder_le_subdivisionDepth R i s n σ)) hdnext

/-! ### The retraction onto the chains of `L` -/

private theorem exists_comp_eq_ιChainComplex_comp_subdivisionApprox {n : ℕ} (σ : K _⦋n⦌) :
    ∃ g : R ⟶ (L.chainComplex R).X n,
      g ≫ (SSet.chainComplexMap i R).f n = K.ιChainComplex σ ≫ (subdivisionApprox R i h).f n :=
  (mem_chainRange_iff _).1 (ιChainComplex_comp_subdivisionApprox_mem_chainRange hs hh hfin σ)

/-- The degreewise factorisation of the approximation through the chains of `L`, obtained by
choosing a factorisation on each summand. -/
private def subdivisionRetractionX (n : ℕ) : (K.chainComplex R).X n ⟶ (L.chainComplex R).X n :=
  Cofan.IsColimit.desc (K.isColimitChainComplexXCofan R n) fun σ ↦
    (exists_comp_eq_ιChainComplex_comp_subdivisionApprox hs hh hfin σ).choose

@[reassoc]
private lemma ιChainComplex_subdivisionRetractionX {n : ℕ} (σ : K _⦋n⦌) :
    K.ιChainComplex σ ≫ subdivisionRetractionX hs hh hfin n =
      (exists_comp_eq_ιChainComplex_comp_subdivisionApprox hs hh hfin σ).choose :=
  Cofan.IsColimit.fac _ _ σ

@[reassoc (attr := simp)]
private lemma subdivisionRetractionX_comp_chainComplexMap_f (n : ℕ) :
    subdivisionRetractionX hs hh hfin n ≫ (SSet.chainComplexMap i R).f n =
      (subdivisionApprox R i h).f n := by
  ext σ
  rw [← Category.assoc, ιChainComplex_subdivisionRetractionX]
  exact (exists_comp_eq_ιChainComplex_comp_subdivisionApprox hs hh hfin σ).choose_spec

variable [Mono i]

/-- **The retraction of the chains of `K` onto the chains of `L`** obtained from the approximation
`TauCeti.subdivisionApprox`. -/
def subdivisionRetraction : K.chainComplex R ⟶ L.chainComplex R where
  f := subdivisionRetractionX hs hh hfin
  comm' a b _ := by
    apply (cancel_mono ((SSet.chainComplexMap i R).f b)).1
    rw [Category.assoc, ← HomologicalComplex.Hom.comm, ← Category.assoc,
      subdivisionRetractionX_comp_chainComplexMap_f, Category.assoc,
      subdivisionRetractionX_comp_chainComplexMap_f, HomologicalComplex.Hom.comm]

@[reassoc (attr := simp)]
lemma subdivisionRetraction_comp_chainComplexMap :
    subdivisionRetraction hs hh hfin ≫ SSet.chainComplexMap i R = subdivisionApprox R i h := by
  ext n : 1
  exact subdivisionRetractionX_comp_chainComplexMap_f hs hh hfin n

@[reassoc (attr := simp)]
lemma chainComplexMap_comp_subdivisionRetraction :
    SSet.chainComplexMap i R ≫ subdivisionRetraction hs hh hfin = 𝟙 _ := by
  apply (cancel_mono (SSet.chainComplexMap i R)).1
  rw [Category.assoc, subdivisionRetraction_comp_chainComplexMap,
    chainComplexMap_comp_subdivisionApprox, Category.id_comp]

/-- **The chains of `L` are a deformation retract of the chains of `K`.**  Let `i : L ⟶ K` be a
monomorphism of simplicial sets, and `h` a chain homotopy from the identity of the chains of `K`
to a chain endomorphism `s`.  If `s` and the components of `h` preserve the chains of `L`, and
every simplex of `K` becomes a chain of `L` after finitely many applications of `s`, then the
inclusion of the chains of `L` is a chain homotopy equivalence, whose homotopy inverse
`TauCeti.subdivisionRetraction` is even a strict retraction. -/
def chainComplexMapHomotopyEquivOfSubdivision :
    HomotopyEquiv (L.chainComplex R) (K.chainComplex R) where
  hom := SSet.chainComplexMap i R
  inv := subdivisionRetraction hs hh hfin
  homotopyHomInvId := Homotopy.ofEq (chainComplexMap_comp_subdivisionRetraction hs hh hfin)
  homotopyInvHomId := (Homotopy.ofEq (subdivisionRetraction_comp_chainComplexMap hs hh hfin)).trans
    (subdivisionApproxHomotopy R i h).symm

@[simp]
lemma chainComplexMapHomotopyEquivOfSubdivision_hom :
    (chainComplexMapHomotopyEquivOfSubdivision hs hh hfin).hom = SSet.chainComplexMap i R :=
  (rfl)


end TauCeti
