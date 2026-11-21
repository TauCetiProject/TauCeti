/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Prod
public import TauCeti.Algebra.Module.Projective.Complement
public import TauCeti.Algebra.Module.Submodule.Finite
public import TauCeti.LinearAlgebra.TensorProduct.Kernel
public import TauCeti.LinearAlgebra.TensorProduct.Quotient
public import TauCeti.RingTheory.Flat.Reduced
public import TauCeti.RingTheory.Spectrum.Prime.FiberDimension

/-!
# Linear maps of constant rank and intersections of direct summands

This file is the module-theoretic form of two facts about vector bundles over a reduced base: the
kernel of a morphism of vector bundles of constant rank is a subbundle, and two subbundles whose
fibres meet in subspaces of constant dimension intersect in a subbundle whose fibres are the
intersections of the fibres.

Let `R` be a reduced commutative ring and `f : M → N` a linear map from a finite module to a finite
projective module. If the fibre dimension `p ↦ dim κ(p) ⊗ (N ⧸ range f)` of its cokernel is
locally constant on `Spec R`, then the cokernel is projective. Consequently the range of `f` is a
direct summand of `N`, the kernel of `f` is a direct summand of `M`
(`LinearMap.isComplemented_ker_of_projective_quotient`), and formation of the kernel
commutes with every extension of scalars (`LinearMap.ker_baseChange_of_flat_quotient_range`).

For two direct summands `E₁` and `E₂` of a finite projective module `E` this is applied to
`E → E ⧸ E₁ × E ⧸ E₂`, whose kernel is `E₁ ⊓ E₂`. If the dimension of the intersection of the fibres
`κ(p) ⊗ E₁` and `κ(p) ⊗ E₂` inside `κ(p) ⊗ E` is locally constant, then `E₁ ⊓ E₂` is a direct
summand of `E`, its rank at `p` is that dimension, and for every coefficient algebra `A` the
extension `A ⊗ (E₁ ⊓ E₂)` is the intersection of `A ⊗ E₁` and `A ⊗ E₂`. Over a Jacobson ring, for
instance an algebra of finite type over a field, it suffices to know the dimension of the
intersection of the fibres at maximal ideals.

The reduced hypothesis cannot be dropped. Over the dual numbers `k[ε]`, the lines spanned by
`(1, 0)` and `(1, ε)` in `k[ε]²` are direct summands whose closed fibres meet in a line, but their
intersection is the submodule spanned by `(ε, 0)`, isomorphic to `k`, which is not a direct
summand.

## Main declarations

* `LinearMap.finrank_fiber_quotient_range_add_finrank_fiber`: the fibre rank-nullity formula
  `dim κ(p) ⊗ (N ⧸ range f) + dim κ(p) ⊗ M = dim κ(p) ⊗ N + dim ker (κ(p) ⊗ f)`.
* `LinearMap.finrank_fiber_ker_add_finrank_fiber`: the fibre dimension of the kernel of a map with
  projective cokernel into a projective module.
* `LinearMap.projective_quotient_range_of_isLocallyConstant`: over a reduced ring, a map from a
  finite module to a finite projective module whose cokernel has locally constant fibre dimension
  has projective cokernel.
* `Submodule.ker_baseChange_mkQ_prod_mkQ`: the kernel of `A ⊗ E → A ⊗ (E ⧸ E₁ × E ⧸ E₂)` is the
  intersection of `A ⊗ E₁` and `A ⊗ E₂` inside `A ⊗ E`.
* `Submodule.isComplemented_inf_of_isLocallyConstant`,
  `Submodule.baseChange_inf_of_isLocallyConstant`, `Submodule.rankAtStalk_inf_of_isLocallyConstant`:
  the intersection of two direct summands whose fibres meet in locally constant dimension is a
  direct summand, commutes with extension of scalars, and has the expected rank.
* `Submodule.finrank_baseChange_inf_eq_of_isJacobsonRing`: over a Jacobson ring, the dimensions
  of the intersections of the fibres are determined at maximal ideals.

## References

* C. Breuil, E. Hellmann, B. Schraen, *A local model for the trianguline variety and applications*,
  Publ. Math. IHÉS 130 (2019), Lemma 2.2.2.
* The Stacks Project, Tag 00NX, finite locally free modules.
-/

public section

open TensorProduct Module

namespace LinearMap

section Rank

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [Module.Finite R M] [Module.Finite R N] (f : M →ₗ[R] N)

/-- The fibre rank-nullity formula: at each prime `p`, the dimension of the fibre of the cokernel
of `f` plus that of `M` is the dimension of the fibre of `N` plus the dimension of the kernel of
`f` on fibres. -/
theorem finrank_fiber_quotient_range_add_finrank_fiber (p : PrimeSpectrum R) :
    finrank p.asIdeal.ResidueField (p.asIdeal.Fiber (N ⧸ range f)) +
        finrank p.asIdeal.ResidueField (p.asIdeal.Fiber M) =
      finrank p.asIdeal.ResidueField (p.asIdeal.Fiber N) +
        finrank p.asIdeal.ResidueField (ker (f.baseChange p.asIdeal.ResidueField)) := by
  rw [(f.cokernelBaseChangeEquiv (S := p.asIdeal.ResidueField)).finrank_eq,
    ← (f.baseChange p.asIdeal.ResidueField).finrank_range_add_finrank_ker,
    ← (range (f.baseChange p.asIdeal.ResidueField)).finrank_quotient_add_finrank]
  omega

/-- If the cokernel of a map into a projective module is projective, the dimension of the fibre
of its kernel is determined by the fibre dimensions of its source, target and cokernel. -/
theorem finrank_fiber_ker_add_finrank_fiber [Module.Projective R N]
    [Module.Projective R (N ⧸ range f)] (p : PrimeSpectrum R) :
    finrank p.asIdeal.ResidueField (p.asIdeal.Fiber (ker f)) +
        finrank p.asIdeal.ResidueField (p.asIdeal.Fiber N) =
      finrank p.asIdeal.ResidueField (p.asIdeal.Fiber M) +
        finrank p.asIdeal.ResidueField (p.asIdeal.Fiber (N ⧸ range f)) := by
  obtain ⟨q, hq⟩ := f.isComplemented_range_of_projective_quotient
  obtain ⟨q', hq'⟩ := f.isComplemented_ker_of_projective_quotient
  -- `M ≅ ker f × range f` and `N ≅ range f × (N ⧸ range f)`.
  let eM : M ≃ₗ[R] ker f × range f :=
    (Submodule.prodEquivOfIsCompl _ _ hq').symm ≪≫ₗ
      LinearEquiv.prodCongr (LinearEquiv.refl R _)
        ((Submodule.quotientEquivOfIsCompl _ _ hq').symm ≪≫ₗ f.quotKerEquivRange)
  let eN : N ≃ₗ[R] range f × (N ⧸ range f) :=
    (Submodule.prodEquivOfIsCompl _ _ hq).symm ≪≫ₗ
      LinearEquiv.prodCongr (LinearEquiv.refl R _) (Submodule.quotientEquivOfIsCompl _ _ hq).symm
  have := Module.Finite.of_isCompl hq'
  have hM := (eM.baseChange R p.asIdeal.ResidueField _ _).finrank_eq
  have hN := (eN.baseChange R p.asIdeal.ResidueField _ _).finrank_eq
  rw [Ideal.finrank_fiber_prod] at hM hN
  -- Unfold the abbreviation `Ideal.Fiber` so that `omega` sees the same atoms everywhere.
  dsimp only [Ideal.Fiber] at hM hN ⊢
  omega

end Rank

section Reduced

variable {R M N : Type*} [CommRing R] [IsReduced R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] [Module.Finite R M] [Module.Finite R N] [Module.Projective R N]
  (f : M →ₗ[R] N)

/-- Over a reduced ring, a map from a finite module to a finite projective module whose cokernel
has locally constant fibre dimension on `Spec R` has projective cokernel. -/
theorem projective_quotient_range_of_isLocallyConstant
    (h : IsLocallyConstant fun p : PrimeSpectrum R ↦
      finrank p.asIdeal.ResidueField (p.asIdeal.Fiber (N ⧸ range f))) :
    Module.Projective R (N ⧸ range f) := by
  have := Module.finitePresentation_of_projective R N
  have : Module.FinitePresentation R (N ⧸ range f) :=
    Module.finitePresentation_of_surjective _ (range f).mkQ_surjective (by simp)
  exact Module.projective_of_isLocallyConstant_finrank_fiber _ h

end Reduced

end LinearMap

namespace Submodule

open LinearMap (ker range)

section BaseChange

variable {R E : Type*} [CommRing R] [AddCommGroup E] [Module R E] (A : Type*) [Ring A]
  [Algebra R A] (E₁ E₂ : Submodule R E)

/-- The kernel of the extension of scalars of `E → E ⧸ E₁ × E ⧸ E₂` is the intersection of the
extensions of `E₁` and `E₂`. -/
theorem ker_baseChange_mkQ_prod_mkQ :
    ker ((E₁.mkQ.prod E₂.mkQ).baseChange A) = E₁.baseChange A ⊓ E₂.baseChange A := by
  have h : (TensorProduct.prodRight R A A (E ⧸ E₁) (E ⧸ E₂)).toLinearMap ∘ₗ
      (E₁.mkQ.prod E₂.mkQ).baseChange A = (E₁.mkQ.baseChange A).prod (E₂.mkQ.baseChange A) := by
    ext x <;> simp
  rw [← LinearEquiv.ker_comp (TensorProduct.prodRight R A A (E ⧸ E₁) (E ⧸ E₂)), h,
    LinearMap.ker_prod, LinearMap.ker_baseChange_of_surjective A _ E₁.mkQ_surjective,
    LinearMap.ker_baseChange_of_surjective A _ E₂.mkQ_surjective, ker_mkQ, ker_mkQ]

end BaseChange

variable {R E : Type*} [CommRing R] [AddCommGroup E] [Module R E] [Module.Finite R E]
  [Module.Projective R E] {E₁ E₂ : Submodule R E}

/-- The fibre rank-nullity formula for `E → E ⧸ E₁ × E ⧸ E₂`, whose fibrewise kernel is the
intersection of the fibres of `E₁` and `E₂`. -/
private theorem finrank_fiber_quotient_range_mkQ_prod_mkQ (h₁ : IsComplemented E₁)
    (h₂ : IsComplemented E₂) (p : PrimeSpectrum R) :
    finrank p.asIdeal.ResidueField
        (p.asIdeal.Fiber (((E ⧸ E₁) × (E ⧸ E₂)) ⧸ range (E₁.mkQ.prod E₂.mkQ))) +
        rankAtStalk E p =
      rankAtStalk ((E ⧸ E₁) × (E ⧸ E₂)) p + finrank p.asIdeal.ResidueField
        ↥(E₁.baseChange p.asIdeal.ResidueField ⊓ E₂.baseChange p.asIdeal.ResidueField) := by
  have := Module.Projective.quotient_of_isCompl h₁.choose_spec
  have := Module.Projective.quotient_of_isCompl h₂.choose_spec
  rw [rankAtStalk_eq, rankAtStalk_eq, ← ker_baseChange_mkQ_prod_mkQ]
  exact (E₁.mkQ.prod E₂.mkQ).finrank_fiber_quotient_range_add_finrank_fiber p

section Reduced

variable [IsReduced R]

/-- Over a reduced ring, `E → E ⧸ E₁ × E ⧸ E₂` has projective cokernel when the intersections of
the fibres of the direct summands `E₁` and `E₂` have locally constant dimension. -/
private theorem projective_quotient_range_mkQ_prod_mkQ (h₁ : IsComplemented E₁)
    (h₂ : IsComplemented E₂)
    (h : IsLocallyConstant fun p : PrimeSpectrum R ↦ finrank p.asIdeal.ResidueField
      ↥(E₁.baseChange p.asIdeal.ResidueField ⊓ E₂.baseChange p.asIdeal.ResidueField)) :
    Module.Projective R (((E ⧸ E₁) × (E ⧸ E₂)) ⧸ range (E₁.mkQ.prod E₂.mkQ)) := by
  have := Module.Projective.quotient_of_isCompl h₁.choose_spec
  have := Module.Projective.quotient_of_isCompl h₂.choose_spec
  have := Module.finitePresentation_of_projective R E
  have := Module.finitePresentation_of_projective R ((E ⧸ E₁) × (E ⧸ E₂))
  refine (E₁.mkQ.prod E₂.mkQ).projective_quotient_range_of_isLocallyConstant ?_
  -- The fibre dimension of the cokernel is `rk (E ⧸ E₁ × E ⧸ E₂) + dim (fibre meet) - rk E`.
  have hc := ((isLocallyConstant_rankAtStalk (R := R) (M := (E ⧸ E₁) × (E ⧸ E₂))).comp₂ h
    (· + ·)).comp₂ (isLocallyConstant_rankAtStalk (R := R) (M := E)) (· - ·)
  convert hc using 1
  ext p
  have := finrank_fiber_quotient_range_mkQ_prod_mkQ h₁ h₂ p
  omega

/-- **Intersection of direct summands.** Over a reduced ring, if the fibres of two direct
summands `E₁` and `E₂` of a finite projective module `E` meet in subspaces of locally constant
dimension, then `E₁ ⊓ E₂` is a direct summand of `E`. -/
theorem isComplemented_inf_of_isLocallyConstant (h₁ : IsComplemented E₁) (h₂ : IsComplemented E₂)
    (h : IsLocallyConstant fun p : PrimeSpectrum R ↦ finrank p.asIdeal.ResidueField
      ↥(E₁.baseChange p.asIdeal.ResidueField ⊓ E₂.baseChange p.asIdeal.ResidueField)) :
    IsComplemented (E₁ ⊓ E₂) := by
  have := Module.Projective.quotient_of_isCompl h₁.choose_spec
  have := Module.Projective.quotient_of_isCompl h₂.choose_spec
  have := projective_quotient_range_mkQ_prod_mkQ h₁ h₂ h
  simpa using (E₁.mkQ.prod E₂.mkQ).isComplemented_ker_of_projective_quotient

/-- Over a reduced ring, if the fibres of two direct summands `E₁` and `E₂` of a finite projective
module meet in subspaces of locally constant dimension, then the formation of `E₁ ⊓ E₂` commutes
with every extension of scalars: `A ⊗ (E₁ ⊓ E₂)` is the intersection of `A ⊗ E₁` and `A ⊗ E₂`. -/
theorem baseChange_inf_of_isLocallyConstant (h₁ : IsComplemented E₁) (h₂ : IsComplemented E₂)
    (h : IsLocallyConstant fun p : PrimeSpectrum R ↦ finrank p.asIdeal.ResidueField
      ↥(E₁.baseChange p.asIdeal.ResidueField ⊓ E₂.baseChange p.asIdeal.ResidueField))
    (A : Type*) [Ring A] [Algebra R A] :
    (E₁ ⊓ E₂).baseChange A = E₁.baseChange A ⊓ E₂.baseChange A := by
  have := projective_quotient_range_mkQ_prod_mkQ h₁ h₂ h
  rw [← ker_baseChange_mkQ_prod_mkQ, LinearMap.ker_baseChange_of_flat_quotient_range,
    LinearMap.ker_prod, ker_mkQ, ker_mkQ]

/-- Over a reduced ring, if the fibres of two direct summands `E₁` and `E₂` of a finite projective
module meet in subspaces of locally constant dimension, then the rank of the projective module
`E₁ ⊓ E₂` at `p` is the dimension of the intersection of the fibres of `E₁` and `E₂` at `p`. -/
theorem rankAtStalk_inf_of_isLocallyConstant (h₁ : IsComplemented E₁) (h₂ : IsComplemented E₂)
    (h : IsLocallyConstant fun p : PrimeSpectrum R ↦ finrank p.asIdeal.ResidueField
      ↥(E₁.baseChange p.asIdeal.ResidueField ⊓ E₂.baseChange p.asIdeal.ResidueField))
    (p : PrimeSpectrum R) :
    rankAtStalk ↥(E₁ ⊓ E₂) p = finrank p.asIdeal.ResidueField
      ↥(E₁.baseChange p.asIdeal.ResidueField ⊓ E₂.baseChange p.asIdeal.ResidueField) := by
  have := Module.Projective.quotient_of_isCompl h₁.choose_spec
  have := Module.Projective.quotient_of_isCompl h₂.choose_spec
  have := projective_quotient_range_mkQ_prod_mkQ h₁ h₂ h
  obtain ⟨q, hq⟩ := isComplemented_inf_of_isLocallyConstant h₁ h₂ h
  have := Module.Finite.of_isCompl hq
  have := Module.Projective.of_isCompl hq
  have hker := (E₁.mkQ.prod E₂.mkQ).finrank_fiber_ker_add_finrank_fiber p
  rw [LinearMap.ker_prod, ker_mkQ, ker_mkQ] at hker
  have := finrank_fiber_quotient_range_mkQ_prod_mkQ h₁ h₂ p
  simp only [rankAtStalk_eq] at this ⊢
  omega

end Reduced

/-- Over a Jacobson ring, for instance an algebra of finite type over a field, the dimensions of
the intersections of the fibres of two direct summands `E₁` and `E₂` of a finite projective module
are determined at the maximal ideals: if they are given there by a locally constant function `a`,
then they are given by `a` at every prime. -/
theorem finrank_baseChange_inf_eq_of_isJacobsonRing [IsJacobsonRing R] (h₁ : IsComplemented E₁)
    (h₂ : IsComplemented E₂) {a : PrimeSpectrum R → ℕ} (ha : IsLocallyConstant a)
    (h : ∀ m : PrimeSpectrum R, m.asIdeal.IsMaximal → finrank m.asIdeal.ResidueField
      ↥(E₁.baseChange m.asIdeal.ResidueField ⊓ E₂.baseChange m.asIdeal.ResidueField) = a m)
    (p : PrimeSpectrum R) :
    finrank p.asIdeal.ResidueField
      ↥(E₁.baseChange p.asIdeal.ResidueField ⊓ E₂.baseChange p.asIdeal.ResidueField) = a p := by
  have := Module.Projective.quotient_of_isCompl h₁.choose_spec
  have := Module.Projective.quotient_of_isCompl h₂.choose_spec
  have := Module.finitePresentation_of_projective R E
  have := Module.finitePresentation_of_projective R ((E ⧸ E₁) × (E ⧸ E₂))
  -- Values of locally constant functions agree at a prime and at its specializations.
  have hsp {g : PrimeSpectrum R → ℕ} (hg : IsLocallyConstant g) :
      ∀ ⦃m : PrimeSpectrum R⦄, p ≤ m → g m = g p := fun m hpm ↦
    (((PrimeSpectrum.le_iff_specializes p m).mp hpm).map hg.continuous).eq.symm
  have hE := hsp (isLocallyConstant_rankAtStalk (R := R) (M := E))
  have hN := hsp (isLocallyConstant_rankAtStalk (R := R) (M := (E ⧸ E₁) × (E ⧸ E₂)))
  -- At a closed point specializing `p`, the cokernel of `E → E ⧸ E₁ × E ⧸ E₂` has fibre
  -- dimension `rk (E ⧸ E₁ × E ⧸ E₂) + a - rk E`, all three terms evaluated at `p`.
  have hmax (m : Ideal R) (hm : m.IsMaximal) (hpm : p.asIdeal ≤ m) :
      finrank m.ResidueField
          (m.Fiber (((E ⧸ E₁) × (E ⧸ E₂)) ⧸ range (E₁.mkQ.prod E₂.mkQ))) + rankAtStalk E p =
        rankAtStalk ((E ⧸ E₁) × (E ⧸ E₂)) p + a p := by
    have hpm' : p ≤ ⟨m, hm.isPrime⟩ := (PrimeSpectrum.asIdeal_le_asIdeal _ _).mp hpm
    have hm' := finrank_fiber_quotient_range_mkQ_prod_mkQ h₁ h₂ ⟨m, hm.isPrime⟩
    rw [h ⟨m, hm.isPrime⟩ hm, hE hpm', hN hpm', hsp ha hpm'] at hm'
    exact hm'
  -- Hence the cokernel has the same fibre dimension at `p`.
  have hk := Ideal.finrank_fiber_eq_of_forall_isMaximal p.asIdeal
    (((E ⧸ E₁) × (E ⧸ E₂)) ⧸ range (E₁.mkQ.prod E₂.mkQ))
    (k := rankAtStalk ((E ⧸ E₁) × (E ⧸ E₂)) p + a p - rankAtStalk E p) fun m hm hpm ↦ by
      have := hmax m hm hpm
      omega
  obtain ⟨m, hm, hpm⟩ := p.asIdeal.exists_le_maximal p.isPrime.ne_top
  have := hmax m hm hpm
  have := finrank_fiber_quotient_range_mkQ_prod_mkQ h₁ h₂ p
  omega

end Submodule
