/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Generator.Basic
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Kernel.Exact
import TauCeti.Algebra.AlgebraicGroup.BaseChange.Naturality
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Kernel.Tensor
import TauCeti.GroupTheory.Coset.Fiber
import TauCeti.RingTheory.Norm.Projective

/-!
# Generators of an extension of finite free group schemes

Let `1 → G₁ → G → G₂ → 1` be a short exact sequence of affine group schemes over `Spec R` which
are finite and free over `R`. In coordinate Hopf algebras it is a pair of morphisms
`p : O(G₂) ⟶ O(G)` and `i : O(G) ⟶ O(G₁)` with `TauCeti.CommHopfAlgCat.IsShortExact p i`. Let
`1 → A₁ → A → A₂ → 1` be a short exact sequence of finite groups, given by `j : A₁ →* A` and
`q : A →* A₂`, and let `φ₁ : A₁ →* G₁(R)`, `φ : A →* G(R)` and `φ₂ : A₂ →* G₂(R)` be compatible
homomorphisms to the points. This file proves Katz–Mazur 1.11.3: if `φ₁` is an `A₁`-generator of
`G₁` and `φ₂` is an `A₂`-generator of `G₂`, then `φ` is an `A`-generator of `G`
(`TauCeti.IsAGenerator.of_isShortExact`). No hypothesis is placed on `R`; in particular the orders
of the groups need not be invertible, which is the case of interest for Drinfeld level structures.
The converse is false in general (Katz–Mazur 1.11.4–1.11.5,
`TauCeti.RootsOfUnityGroup.exists_not_isAGenerator`).

## Main results

* `TauCeti.IsAGenerator.of_isShortExact`: an `A₁`-generator of `G₁` and a compatible
  `A₂`-generator of `G₂` give an `A`-generator of `G`.

## Implementation notes

The proof is transitivity of the norm. The quotient map `G → G₂` is finite and faithfully flat,
hence finite locally free (`TauCeti.CommHopfAlgCat.IsShortExact.moduleProjective`), and
`Norm_{G/R} = Norm_{G₂/R} ∘ Norm_{G/G₂}`
(`Algebra.norm_projectiveNorm`). The full set of sections `φ₂` evaluates `Norm_{G₂/R}`. Pulled
back to `G`, the norm `Norm_{G/G₂}(b)` is the norm along the first projection of the kernel pair
`G ×_{G₂} G ≅ G × G₁` (`TauCeti.CommHopfAlgCat.kernelPairTensorEquiv`) of the pullback of `b` by
the second projection, which the full set of sections `φ₁` evaluates as the product of the
translates of `b` by the points `φ₁ a₁`. Taking
values at `φ a` for one `a` above each element of `A₂` gives the product of `b` over all the points
`φ (a * j a₁)`, that is over all of `A`. Since a full set of sections is defined by this identity
after every base change, the argument is run after an arbitrary base change `R → T`, using
`TauCeti.CommHopfAlgCat.IsShortExact.baseChange`.

## References

* N. M. Katz, B. Mazur, *Arithmetic Moduli of Elliptic Curves*, Annals of Mathematics Studies
  108, Princeton University Press, 1985, 1.11.3.
-/

public section

open CategoryTheory WithConv TensorProduct TauCeti.CommHopfAlgCat

namespace TauCeti

universe u v

variable {R : Type u} [CommRing R] {Q G N : _root_.CommHopfAlgCat.{v} R} {p : Q ⟶ G} {i : G ⟶ N}

/-- The value of a point `f` of `G` at the translate of `b` by the point `s ∘ i` of `G` coming from
a point `s` of `N` is the value of the convolution `f * (s ∘ i)` at `b`. -/
private theorem apply_sectionBaseChange_map_comul (f : G →ₐ[R] R) (s : N →ₐ[R] R) (b : G) :
    f (s.sectionBaseChange G
        (Algebra.TensorProduct.map (AlgHom.id R G) i.hom.toAlgHom (Coalgebra.comul (R := R) b))) =
      (toConv f * toConv (s.comp i.hom.toAlgHom)).ofConv b := by
  rw [AlgHom.convMul_apply]
  induction Coalgebra.comul (R := R) b using TensorProduct.inductionOn with
  | tmul x y => simp
  | add x y hx hy => simp only [map_add, hx, hy]

variable {A₁ A A₂ : Type*} [Group A₁] [Group A] [Group A₂] [Fintype A₁] [Fintype A] [Fintype A₂]
  {j : A₁ →* A} {q : A →* A₂} {φ₁ : A₁ →* WithConv (N →ₐ[R] R)} {φ : A →* WithConv (G →ₐ[R] R)}
  {φ₂ : A₂ →* WithConv (Q →ₐ[R] R)}

/-- Katz–Mazur 1.11.3 without base change: the norm of a function `b` on `G` over `R` is the
product of its values at the points `φ a`. -/
private theorem norm_eq_prod_of_isShortExact [Module.Free R Q] [Module.Finite R Q]
    [Module.Free R G] [Module.Finite R G] [Module.Free R N] [Module.Finite R N]
    (h : IsShortExact p i) (hj : Function.Injective j) (hq : Function.Surjective q)
    (hjq : q.ker = j.range) (h₁ : (BialgHom.mapDomain i.hom).comp φ₁ = φ.comp j)
    (h₂ : (BialgHom.mapDomain p.hom).comp φ = φ₂.comp q) (hφ₁ : IsAGenerator φ₁)
    (hφ₂ : IsAGenerator φ₂) (b : G) :
    Algebra.norm R b = ∏ a, (φ a).ofConv b := by
  let := p.hom.toAlgHom.toAlgebra
  have : IsScalarTower R Q G :=
    IsScalarTower.of_algebraMap_eq fun r ↦ (p.hom.toAlgHom.commutes r).symm
  have : Module.Finite Q G := Module.Finite.of_restrictScalars_finite R Q G
  have := h.moduleProjective
  -- the kernel pair `G ×_{G₂} G` of `G → G₂` is `G × G₁`, by `(g, n) ↦ (g, g n)`
  let e : G ⊗[Q] G ≃ₐ[G] G ⊗[R] N := (kernelPairTensorEquiv p).trans
    (Algebra.TensorProduct.congr AlgEquiv.refl (_root_.CommHopfAlgCat.ofIso h.kernelIso).toAlgEquiv)
  have he : e (1 ⊗ₜ b) = Algebra.TensorProduct.map (AlgHom.id R G) i.hom.toAlgHom
      (Coalgebra.comul (R := R) b) := by
    have hki (y : G) : _root_.CommHopfAlgCat.ofIso h.kernelIso
        (Ideal.Quotient.mk (kernelHopfIdeal p).toIdeal y) = i.hom y := by
      rw [← Ideal.Quotient.mkₐ_eq_mk R, ← mkQuotient_apply]
      exact congrArg (fun f ↦ f.hom y) h.mkQuotient_comp_kernelIso_hom
    rw [AlgEquiv.trans_apply, kernelPairTensorEquiv_tmul, ← Algebra.TensorProduct.one_def,
      one_mul]
    induction Coalgebra.comul (R := R) b using TensorProduct.inductionOn with
    | tmul x y => simp [hki]
    | add x y hx hy => simp only [map_add, hx, hy]
  -- at a point `φ a`, the norm of `b` over `Q` is the product of `b` over the coset `a A₁`
  have hnorm (a : A) : (φ₂ (q a)).ofConv (Algebra.projectiveNorm Q b) =
      ∏ a₁, (φ (a * j a₁)).ofConv b := by
    have hpa : (φ₂ (q a)).ofConv = (φ a).ofConv.comp p.hom.toAlgHom :=
      congrArg ofConv (DFunLike.congr_fun h₂ a).symm
    rw [hpa, AlgHom.comp_apply]
    -- `p` is the structure map of the `Q`-algebra `G`
    change (φ a).ofConv (algebraMap Q G (Algebra.projectiveNorm Q b)) = _
    rw [← Algebra.projectiveNorm_baseChange_tmul, ← Algebra.projectiveNorm_eq_of_algEquiv e,
      Algebra.projectiveNorm_eq_norm, (isAGenerator_iff.mp hφ₁).norm_eq, map_prod, he]
    refine Finset.prod_congr rfl fun a₁ _ ↦ ?_
    have ha₁ : toConv ((φ₁ a₁).ofConv.comp i.hom.toAlgHom) = φ (j a₁) :=
      DFunLike.congr_fun h₁ a₁
    rw [apply_sectionBaseChange_map_comul, map_mul, ha₁, toConv_ofConv]
  -- sum over `A` as a double sum over `A₂` and the cosets of `A₁`
  classical
  rw [← Algebra.projectiveNorm_eq_norm, ← Algebra.norm_projectiveNorm (S := Q),
    (isAGenerator_iff.mp hφ₂).norm_eq_prod, ← Fintype.prod_fiberwise q]
  refine Finset.prod_congr rfl fun a₂ _ ↦ ?_
  obtain ⟨a, rfl⟩ := hq a₂
  rw [hnorm, q.prod_fiber_eq_prod_ker_mul_left rfl fun x ↦ (φ x).ofConv b]
  exact Fintype.prod_equiv
    ((MonoidHom.ofInjective hj).trans (MulEquiv.subgroupCongr hjq.symm)).toEquiv _ _ fun _ ↦ rfl

/-- **Generators of an extension** (Katz–Mazur 1.11.3). Let `p : O(G₂) ⟶ O(G)` and
`i : O(G) ⟶ O(G₁)` be a short exact sequence `1 → G₁ → G → G₂ → 1` of finite free affine group
schemes over `R`, and let `j : A₁ →* A` and `q : A →* A₂` be a short exact sequence of finite
groups. Let `φ₁ : A₁ →* G₁(R)`, `φ : A →* G(R)` and `φ₂ : A₂ →* G₂(R)` be compatible with these
maps: `i ∘ φ₁ = φ ∘ j` and `p ∘ φ = φ₂ ∘ q` on points. If `φ₁` is an `A₁`-generator of `G₁` and
`φ₂` is an `A₂`-generator of `G₂`, then `φ` is an `A`-generator of `G`. -/
theorem IsAGenerator.of_isShortExact [Module.Free R Q] [Module.Finite R Q]
    [Module.Finite R G] [Module.Free R N] [Module.Finite R N]
    (h : IsShortExact p i) (hj : Function.Injective j) (hq : Function.Surjective q)
    (hjq : q.ker = j.range) (h₁ : (BialgHom.mapDomain i.hom).comp φ₁ = φ.comp j)
    (h₂ : (BialgHom.mapDomain p.hom).comp φ = φ₂.comp q) (hφ₁ : IsAGenerator φ₁)
    (hφ₂ : IsAGenerator φ₂) : IsAGenerator φ := by
  refine isAGenerator_iff.mpr <| isFullSetOfSections_iff.mpr fun T _ _ _ f ↦ ?_
  have h₁T := BialgHom.mapDomain_comp_pointsBaseChange_comp T i.hom h₁
  have h₂T := BialgHom.mapDomain_comp_pointsBaseChange_comp T p.hom h₂
  simpa [AlgHom.ofConv_pointsBaseChange] using norm_eq_prod_of_isShortExact (h.baseChange T) hj
    hq hjq h₁T h₂T (hφ₁.baseChange T) (hφ₂.baseChange T) f

end TauCeti
