/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.Cap.Basic
public import TauCeti.AlgebraicTopology.Cohomology.Cup.Basic

/-!
# Associativity of the singular cap product

For singular chains and cochains with coefficients in a commutative ring, iterated capping agrees
with capping by the cup product:

`(x ⌢ α) ⌢ β = x ⌢ (α ⌣ β)`.

The equality first holds on chains.  Both sides evaluate an `n`-simplex on the same three faces:
the front `p`-face for `α`, the following `q`-face for `β`, and the back `r`-face retained as
the resulting chain.  It then descends to singular homology and cohomology.

The coefficients are the tensor unit of `ModuleCat k`; its unitors implement both multiplication
of cochain values and their action on chains.  This is the ordinary cap--cup associativity law of
A. Hatcher, *Algebraic Topology*, Section 3.3.
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory AlgebraicTopology Simplicial HomologicalComplex

universe w

namespace TopCat

variable (X : TopCat.{w}) (k : Type w) [CommRing k]

attribute [local instance] hasFiniteCoproducts_of_hasCoproducts
attribute [local instance] HasFiniteBiproducts.of_hasFiniteCoproducts

/-- **Cap--cup associativity on singular chains**: capping successively with cochains `φ` and
`ψ` is capping once with their cup product. -/
lemma capChain_alexanderWhitneyDiagonal_assoc
    {p q r m n : ℕ} (hp : p + m = n) (hq : q + r = m)
    (φ : ((toSSet.obj X).chainComplex (𝟙_ (ModuleCat.{w} k))).X p ⟶ 𝟙_ (ModuleCat.{w} k))
    (ψ : ((toSSet.obj X).chainComplex (𝟙_ (ModuleCat.{w} k))).X q ⟶ 𝟙_ (ModuleCat.{w} k)) :
    TauCeti.ChainComplex.capChain k
        (X.alexanderWhitneyDiagonal (λ_ (𝟙_ (ModuleCat.{w} k))).inv)
        ((toSSet.obj X).chainComplexPairing (ρ_ (𝟙_ (ModuleCat.{w} k))).hom)
        p m n hp φ ≫
      TauCeti.ChainComplex.capChain k
        (X.alexanderWhitneyDiagonal (λ_ (𝟙_ (ModuleCat.{w} k))).inv)
        ((toSSet.obj X).chainComplexPairing (ρ_ (𝟙_ (ModuleCat.{w} k))).hom)
        q r m hq ψ =
      TauCeti.ChainComplex.capChain k
        (X.alexanderWhitneyDiagonal (λ_ (𝟙_ (ModuleCat.{w} k))).inv)
        ((toSSet.obj X).chainComplexPairing (ρ_ (𝟙_ (ModuleCat.{w} k))).hom)
        (p + q) r n (by omega)
        (TauCeti.ChainComplex.cupCochain k
          (X.alexanderWhitneyDiagonal (λ_ (𝟙_ (ModuleCat.{w} k))).inv)
          (ρ_ (𝟙_ (ModuleCat.{w} k))).hom p q (p + q) rfl φ ψ) := by
  subst hp
  subst hq
  apply SSet.chainComplex_hom_ext
  intro σ
  rw [← Category.assoc, ιChainComplex_capChain_alexanderWhitneyDiagonal,
    ιChainComplex_capChain_alexanderWhitneyDiagonal]
  simp only [Category.assoc]
  rw [ιChainComplex_capChain_alexanderWhitneyDiagonal,
    ιChainComplex_cupCochain_alexanderWhitneyDiagonal]
  simp only [
    ← Functor.map_comp_apply, ← op_comp,
    TauCeti.SimplexCategory.subinterval_comp_subinterval _ _ _ _ _ _ rfl,
    Nat.zero_add, Nat.add_zero]
  simp only [whiskerRight_id, Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id,
    Category.comp_id, Iso.cancel_iso_inv_left, Iso.cancel_iso_hom_left]
  apply ConcreteCategory.hom_ext
  intro x
  simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply,
    ModuleCat.MonoidalCategory.leftUnitor_inv_apply,
    ModuleCat.MonoidalCategory.rightUnitor_hom_apply, smul_eq_mul, mul_one,
    ModuleCat.MonoidalCategory.tensorHom_tmul]
  let a : 𝟙_ (ModuleCat.{w} k) ⟶ 𝟙_ (ModuleCat.{w} k) :=
    (toSSet.obj X).ιChainComplex
      ((toSSet.obj X).map (SimplexCategory.subinterval 0 p (by omega)).op σ) ≫ φ
  let b : 𝟙_ (ModuleCat.{w} k) ⟶ 𝟙_ (ModuleCat.{w} k) :=
    (toSSet.obj X).ιChainComplex
      ((toSSet.obj X).map (SimplexCategory.subinterval p q (by omega)).op σ) ≫ ψ
  let c : 𝟙_ (ModuleCat.{w} k) ⟶
      ((toSSet.obj X).chainComplex (𝟙_ (ModuleCat.{w} k))).X r :=
    (toSSet.obj X).ιChainComplex
      ((toSSet.obj X).map (SimplexCategory.subinterval (p + q) r (by omega)).op σ)
  -- The goal is now `c' (ψ (b' (φ (a' x)))) = c' (ψ (b' x) * φ (a' 1))`, where `a'`, `b'`, `c'`
  -- are the three face inclusions `ιChainComplex (X.map (subinterval _ _ _).op σ)`.  This `change`
  -- only refolds `φ (a' _)` and `ψ (b' _)` into the composites `a = a' ≫ φ`, `b = b' ≫ ψ` (and
  -- names `c = c'`), i.e. `ModuleCat.hom_comp` read backwards; `rw [← ModuleCat.comp_apply]`
  -- cannot do this: its reversed pattern `?f (?g ?y)` first matches the outer `c' (ψ _)`.
  change c (b (a x)) = c (b x * a 1)
  have apply_eq {M : ModuleCat.{w} k} (f : 𝟙_ (ModuleCat.{w} k) ⟶ M) (y : k) :
      f y = y • f 1 := by
    rw [← map_smul]
    simp
  rw [apply_eq a x, apply_eq b (x • a 1), apply_eq c ((x • a 1) • b 1),
    apply_eq b x, apply_eq c (x • b 1 * a 1)]
  simp only [smul_eq_mul]
  rw [mul_assoc, mul_assoc, mul_comm (a 1) (b 1)]

/-- The cycle-level form of cap--cup associativity: capping cycles successively by the cocycles
`φ` and `ψ` is capping once by their cup product. -/
private lemma capCycles_comp_capCycles_cupCycles
    {p q r m n : ℕ} (hp : p + m = n) (hq : q + r = m)
    (φ : (X.singularCochainComplex (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k))).cycles p)
    (ψ : (X.singularCochainComplex (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k))).cycles q) :
    TauCeti.ChainComplex.capCycles k
        (X.alexanderWhitneyDiagonal (λ_ (𝟙_ (ModuleCat.{w} k))).inv)
        ((toSSet.obj X).chainComplexPairing (ρ_ (𝟙_ (ModuleCat.{w} k))).hom)
        p m n hp φ ≫
      TauCeti.ChainComplex.capCycles k
        (X.alexanderWhitneyDiagonal (λ_ (𝟙_ (ModuleCat.{w} k))).inv)
        ((toSSet.obj X).chainComplexPairing (ρ_ (𝟙_ (ModuleCat.{w} k))).hom)
        q r m hq ψ =
      TauCeti.ChainComplex.capCycles k
        (X.alexanderWhitneyDiagonal (λ_ (𝟙_ (ModuleCat.{w} k))).inv)
        ((toSSet.obj X).chainComplexPairing (ρ_ (𝟙_ (ModuleCat.{w} k))).hom)
        (p + q) r n (by omega)
        (TauCeti.ChainComplex.cupCycles k
          (X.alexanderWhitneyDiagonal (λ_ (𝟙_ (ModuleCat.{w} k))).inv)
          (ρ_ (𝟙_ (ModuleCat.{w} k))).hom p q (p + q) rfl φ ψ) := by
  apply (cancel_mono (((toSSet.obj X).chainComplex (𝟙_ (ModuleCat.{w} k))).iCycles r)).1
  simp only [Category.assoc, TauCeti.ChainComplex.capCycles_i]
  rw [← Category.assoc, TauCeti.ChainComplex.capCycles_i]
  simp only [Category.assoc]
  apply congrArg (((toSSet.obj X).chainComplex
    (𝟙_ (ModuleCat.{w} k))).iCycles n ≫ ·)
  simpa only [TauCeti.ChainComplex.iCycles_cupCycles] using
    capChain_alexanderWhitneyDiagonal_assoc X k hp hq
      (((X.singularCochainComplex (𝟙_ (ModuleCat.{w} k)) k
        (𝟙_ (ModuleCat.{w} k))).iCycles p).hom φ)
      (((X.singularCochainComplex (𝟙_ (ModuleCat.{w} k)) k
        (𝟙_ (ModuleCat.{w} k))).iCycles q).hom ψ)

/-- **Cap--cup associativity in singular homology**: for ordinary cohomology and homology with
coefficients in a commutative ring, capping successively by `α` and `β` is capping by
`α ⌣ β`. -/
lemma singularCap_assoc
    {p q r m n : ℕ} (hp : p + m = n) (hq : q + r = m)
    (α : X.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) p)
    (β : X.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) q) :
    X.singularCap k (λ_ (𝟙_ (ModuleCat.{w} k))).inv (ρ_ (𝟙_ (ModuleCat.{w} k))).hom
        p m n hp α ≫
      X.singularCap k (λ_ (𝟙_ (ModuleCat.{w} k))).inv (ρ_ (𝟙_ (ModuleCat.{w} k))).hom
        q r m hq β =
      X.singularCap k (λ_ (𝟙_ (ModuleCat.{w} k))).inv (ρ_ (𝟙_ (ModuleCat.{w} k))).hom
        (p + q) r n (by omega)
        (X.singularCup k (λ_ (𝟙_ (ModuleCat.{w} k))).inv (ρ_ (𝟙_ (ModuleCat.{w} k))).hom
          p q (p + q) rfl α β) := by
  obtain ⟨φ, rfl⟩ := HomologicalComplex.moduleCat_homologyπ_surjective _ p α
  obtain ⟨ψ, rfl⟩ := HomologicalComplex.moduleCat_homologyπ_surjective _ q β
  have : Epi (((toSSet.obj X).chainComplex (𝟙_ (ModuleCat.{w} k))).homologyπ n) :=
    (ModuleCat.epi_iff_surjective _).2 (HomologicalComplex.moduleCat_homologyπ_surjective _ n)
  refine (cancel_epi (((toSSet.obj X).chainComplex (𝟙_ (ModuleCat.{w} k))).homologyπ n)).1 ?_
  -- The `homologyπ` squares are stated for `homology`, while `singularCap` is stated for
  -- `singularHomologyFunctor`; the two agree by unfolding, so the squares are applied through
  -- `Eq.trans` and `congrArg`, whose unification sees through it, rather than through `rw`.
  have hp' := singularCap_homologyπ X k (λ_ (𝟙_ (ModuleCat.{w} k))).inv
    (ρ_ (𝟙_ (ModuleCat.{w} k))).hom p m n hp φ
  have hq' := singularCap_homologyπ X k (λ_ (𝟙_ (ModuleCat.{w} k))).inv
    (ρ_ (𝟙_ (ModuleCat.{w} k))).hom q r m hq ψ
  have hpq := singularCap_homologyπ X k (λ_ (𝟙_ (ModuleCat.{w} k))).inv
    (ρ_ (𝟙_ (ModuleCat.{w} k))).hom (p + q) r n (by omega)
    (TauCeti.ChainComplex.cupCycles k
      (X.alexanderWhitneyDiagonal (λ_ (𝟙_ (ModuleCat.{w} k))).inv)
      (ρ_ (𝟙_ (ModuleCat.{w} k))).hom p q (p + q) rfl φ ψ)
  rw [singularCup_homologyπ]
  refine (Category.assoc _ _ _).symm.trans <|
    (congrArg (· ≫ _) hp').trans <| (Category.assoc _ _ _).trans <|
    (congrArg (_ ≫ ·) hq').trans <| (Category.assoc _ _ _).symm.trans <|
    (congrArg (· ≫ _) (capCycles_comp_capCycles_cupCycles X k hp hq φ ψ)).trans hpq.symm

end TopCat
