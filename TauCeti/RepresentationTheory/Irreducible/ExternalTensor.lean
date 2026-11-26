/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Simple
public import Mathlib.RepresentationTheory.FDRep
public import TauCeti.RepresentationTheory.Tensor.External
import TauCeti.Algebra.TensorProduct.SimpleModule
import TauCeti.RepresentationTheory.FDRep.Basic
import TauCeti.RepresentationTheory.OfModule
import TauCeti.RepresentationTheory.Simple.Basic

/-!
# Irreducible representations of a product of monoids

Let `G` and `H` be monoids and `k` a field. The external tensor product `ρ ⊠ σ` of irreducible
representations `ρ` of `G` and `σ` of `H` is an irreducible representation of `G × H` when `k` is
algebraically closed and `ρ` is finite-dimensional (`Representation.isIrreducible_externalTensor`).
This file proves the converse classification:

* over an algebraically closed field, every finite-dimensional irreducible representation of
  `G × H` is equivalent to such an external tensor product of finite-dimensional irreducible
  representations (`Representation.exists_isIrreducible_nonempty_equiv_externalTensor`);
* over any field, `ρ ⊠ σ` and `ρ' ⊠ σ'`, with all four factors irreducible, are equivalent exactly
  when `ρ ≅ ρ'` and `σ ≅ σ'` (`Representation.nonempty_equiv_externalTensor_iff`).

Together they say that `(V, W) ↦ V ⊠ W` is a bijection from pairs of isomorphism classes of simple
objects of `FDRep k G` and `FDRep k H` onto the isomorphism classes of simple objects of
`FDRep k (G × H)` (`FDRep.externalTensor_classification`). No finiteness, compactness or
semisimplicity of the monoids is assumed. For topological monoids the factors of a continuous
representation are again continuous (`FDRep.exists_isContinuous_iso_externalTensor`), so for
compact groups this describes the irreducible classes of the representation ring `R(G × H)`
through those of `R(G)` and `R(H)`.

## The argument

A representation `τ` of `G × H` on `U` is a module over `k[G] ⊗[k] k[H]`, on which `a ⊗ b` acts
by `a` through `G × 1` and by `b` through `1 × H`; these two actions commute because `(g, 1)` and
`(1, h)` do. A subspace stable under this algebra is stable under every `τ (g, h)`, so `U` is a
simple module when `τ` is irreducible. Flath's factorization of simple modules over a tensor
product of algebras (`TauCeti.exists_tensorProduct_equiv_of_isSimpleModule`) writes such a
finite-dimensional module as `V ⊗[k] W` for simple modules `V` over `k[G]` and `W` over `k[H]`,
which are irreducible representations of `G` and `H`
(`TauCeti.Representation.isIrreducible_ofModule'_iff`). Conversely, on `V ⊗[k] W` the algebra
`k[G] ⊗[k] k[H]` acts through `ρ ⊠ σ`, and an equivalence of representations of `G × H` commutes
with this action, so the uniqueness of the factors of a tensor product of simple modules
(`TauCeti.nonempty_linearEquiv_of_tensorPairAction_equiv`) gives the uniqueness statement.

## Main results

* `Representation.exists_isIrreducible_nonempty_equiv_externalTensor`: every finite-dimensional
  irreducible representation of `G × H` over an algebraically closed field is an external tensor
  product of finite-dimensional irreducible representations.
* `Representation.nonempty_equiv_externalTensor_iff`: external tensor products of irreducible
  representations are equivalent exactly when their factors are.
* `FDRep.externalTensor_classification`: every simple object of `FDRep k (G × H)` is an external
  tensor product of simple objects, with factors unique up to isomorphism.

## References

* D. Flath, *Decomposition of representations into tensor products*, in *Automorphic forms,
  representations and L-functions*, Proc. Sympos. Pure Math. 33, Part 1 (1979), 179–183,
  Theorem 1.
* W. Fulton and J. Harris, *Representation Theory: A First Course*, Springer GTM 129 (1991),
  Exercise 2.36.
-/

public section

open scoped MonoidAlgebra TensorProduct
open TauCeti.Representation (isIrreducible_ofModule'_iff)

namespace Representation

universe u

variable {k G H : Type*} [Field k] [Monoid G] [Monoid H]

section TensorAlgebra

variable {U U' : Type*} [AddCommGroup U] [Module k U] [AddCommGroup U'] [Module k U']

/-- The action of `k[G] ⊗[k] k[H]` on the carrier of a representation `τ` of `G × H`: `a ⊗ b` acts
by `a` through `G × 1` and by `b` through `1 × H`. -/
private noncomputable def tensorAlgHom (τ : Representation k (G × H) U) :
    k[G] ⊗[k] k[H] →ₐ[k] Module.End k U :=
  Algebra.TensorProduct.lift (asAlgebraHom (τ.comp (MonoidHom.inl G H)))
    (asAlgebraHom (τ.comp (MonoidHom.inr G H))) fun a b ↦ by
      -- The images of `G × 1` and `1 × H` commute, hence so do the algebras they span.
      have hgh (g : G) (h : H) : Commute (τ (g, 1)) (τ (1, h)) := by
        rw [Commute, SemiconjBy, ← map_mul, ← map_mul]
        simp
      induction a using MonoidAlgebra.induction_linear with
      | zero => exact Commute.zero_left _
      | add a a' ha ha' => rw [map_add]; exact ha.add_left ha'
      | single g c =>
        induction b using MonoidAlgebra.induction_linear with
        | zero => exact Commute.zero_right _
        | add b b' hb hb' => rw [map_add]; exact hb.add_right hb'
        | single h d =>
          rw [asAlgebraHom_single, asAlgebraHom_single]
          exact ((hgh g h).smul_left c).smul_right d

private theorem tensorAlgHom_tmul (τ : Representation k (G × H) U) (a : k[G]) (b : k[H]) :
    tensorAlgHom τ (a ⊗ₜ b) =
      asAlgebraHom (τ.comp (MonoidHom.inl G H)) a * asAlgebraHom (τ.comp (MonoidHom.inr G H)) b :=
  Algebra.TensorProduct.lift_tmul _ _ _ a b

private theorem tensorAlgHom_single_tmul_single (τ : Representation k (G × H) U) (g : G) (h : H) :
    tensorAlgHom τ (MonoidAlgebra.single g 1 ⊗ₜ MonoidAlgebra.single h 1) = τ (g, h) := by
  rw [tensorAlgHom_tmul, asAlgebraHom_single_one, asAlgebraHom_single_one, MonoidHom.comp_apply,
    MonoidHom.comp_apply, ← map_mul]
  simp

private theorem tensorAlgHom_single_tmul_one (τ : Representation k (G × H) U) (g : G) :
    tensorAlgHom τ (MonoidAlgebra.single g 1 ⊗ₜ 1) = τ (g, 1) := by
  simp [tensorAlgHom_tmul]

private theorem tensorAlgHom_one_tmul_single (τ : Representation k (G × H) U) (h : H) :
    tensorAlgHom τ (1 ⊗ₜ MonoidAlgebra.single h 1) = τ (1, h) := by
  simp [tensorAlgHom_tmul]

/-- An equivalence of representations of `G × H` commutes with the actions of `k[G] ⊗[k] k[H]`. -/
private theorem Equiv.apply_tensorAlgHom_apply {τ : Representation k (G × H) U}
    {τ' : Representation k (G × H) U'} (e : τ.Equiv τ') (t : k[G] ⊗[k] k[H]) (x : U) :
    e (tensorAlgHom τ t x) = tensorAlgHom τ' t (e x) := by
  have he (p : G × H) (u : U) : e (τ p u) = τ' p (e u) :=
    LinearMap.congr_fun (e.isIntertwining' p) u
  -- Conjugating by `e` is an algebra map, and it agrees with the action of `τ'` on generators.
  have hconj : ((LinearEquiv.conjAlgEquiv k e.toLinearEquiv).toAlgHom.comp (tensorAlgHom τ)) =
      tensorAlgHom τ' := by
    refine Algebra.TensorProduct.ext (MonoidAlgebra.algHom_ext (fun g ↦ ?_) (Subsingleton.elim _ _))
      (MonoidAlgebra.algHom_ext (fun h ↦ ?_) (Subsingleton.elim _ _)) <;>
    · ext y
      simp [tensorAlgHom_tmul, LinearEquiv.conjAlgEquiv_apply, Equiv.coe_invFun, he]
  have := congrArg (fun F ↦ F t (e x)) hconj
  simpa [LinearEquiv.conjAlgEquiv_apply, Equiv.coe_invFun] using this

variable {V W : Type*} [AddCommGroup V] [Module k V] [Module k[G] V] [IsScalarTower k k[G] V]
  [AddCommGroup W] [Module k W] [Module k[H] W] [IsScalarTower k k[H] W]

/-- On a tensor product `V ⊗[k] W` of modules over `k[G]` and `k[H]`, the algebra
`k[G] ⊗[k] k[H]` acts through the external tensor product of the representations they carry. -/
private theorem tensorPairAction_eq_tensorAlgHom :
    TauCeti.BialgebraModule.tensorPairAction k V W (A := k[G]) (B := k[H]) =
      tensorAlgHom ((ofModule' V).externalTensor (ofModule' W)) := by
  refine Algebra.TensorProduct.ext (MonoidAlgebra.algHom_ext (fun g ↦ ?_) (Subsingleton.elim _ _))
    (MonoidAlgebra.algHom_ext (fun h ↦ ?_) (Subsingleton.elim _ _)) <;>
  · ext v w
    simp [tensorAlgHom_single_tmul_one, tensorAlgHom_one_tmul_single]

end TensorAlgebra

variable {V W V' W' : Type*} [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
  [AddCommGroup V'] [Module k V'] [AddCommGroup W'] [Module k W']

/-- **External tensor products of irreducibles are equivalent exactly when their factors are.**
For representations `ρ`, `ρ'` of a monoid `G` and `σ`, `σ'` of a monoid `H`, all irreducible,
`ρ ⊠ σ ≅ ρ' ⊠ σ'` if and only if `ρ ≅ ρ'` and `σ ≅ σ'`. No finiteness or algebraic closedness is
needed. -/
@[simp]
theorem nonempty_equiv_externalTensor_iff (ρ : Representation k G V) (σ : Representation k H W)
    (ρ' : Representation k G V') (σ' : Representation k H W') [ρ.IsIrreducible] [σ.IsIrreducible]
    [ρ'.IsIrreducible] [σ'.IsIrreducible] :
    Nonempty ((ρ.externalTensor σ).Equiv (ρ'.externalTensor σ')) ↔
      Nonempty (ρ.Equiv ρ') ∧ Nonempty (σ.Equiv σ') := by
  refine ⟨fun ⟨e⟩ ↦ ?_, fun ⟨⟨e⟩, ⟨f⟩⟩ ↦ ⟨e.externalTensor f⟩⟩
  -- Make the group algebras act on the four carriers through the four representations.
  let _ : Module k[G] V := Module.compHom V ρ.asAlgebraHom.toRingHom
  let _ : Module k[H] W := Module.compHom W σ.asAlgebraHom.toRingHom
  let _ : Module k[G] V' := Module.compHom V' ρ'.asAlgebraHom.toRingHom
  let _ : Module k[H] W' := Module.compHom W' σ'.asAlgebraHom.toRingHom
  -- `Module.compHom` acts through the algebra map; these equations hold by definition.
  have hV (a : k[G]) (v : V) : a • v = ρ.asAlgebraHom a v := rfl
  have hW (b : k[H]) (w : W) : b • w = σ.asAlgebraHom b w := rfl
  have hV' (a : k[G]) (v : V') : a • v = ρ'.asAlgebraHom a v := rfl
  have hW' (b : k[H]) (w : W') : b • w = σ'.asAlgebraHom b w := rfl
  have : IsScalarTower k k[G] V := ⟨fun c a v ↦ by simp [hV]⟩
  have : IsScalarTower k k[H] W := ⟨fun c b w ↦ by simp [hW]⟩
  have : IsScalarTower k k[G] V' := ⟨fun c a v ↦ by simp [hV']⟩
  have : IsScalarTower k k[H] W' := ⟨fun c b w ↦ by simp [hW']⟩
  -- The representations read off these modules are the given ones.
  have hρ : ofModule' V = ρ := by ext g v; simp [hV]
  have hσ : ofModule' W = σ := by ext h w; simp [hW]
  have hρ' : ofModule' V' = ρ' := by ext g v; simp [hV']
  have hσ' : ofModule' W' = σ' := by ext h w; simp [hW']
  have : IsSimpleModule k[G] V := (isIrreducible_ofModule'_iff V).1 (hρ ▸ ‹_›)
  have : IsSimpleModule k[H] W := (isIrreducible_ofModule'_iff W).1 (hσ ▸ ‹_›)
  have : IsSimpleModule k[G] V' := (isIrreducible_ofModule'_iff V').1 (hρ' ▸ ‹_›)
  have : IsSimpleModule k[H] W' := (isIrreducible_ofModule'_iff W').1 (hσ' ▸ ‹_›)
  obtain ⟨⟨f⟩, ⟨f'⟩⟩ := TauCeti.nonempty_linearEquiv_of_tensorPairAction_equiv
    (A := k[G]) (B := k[H]) e.toLinearEquiv fun t x ↦ by
      rw [tensorPairAction_eq_tensorAlgHom, tensorPairAction_eq_tensorAlgHom, hρ, hσ, hρ', hσ']
      exact e.apply_tensorAlgHom_apply t x
  refine ⟨⟨.mk (f.restrictScalars k) fun g ↦ LinearMap.ext fun v ↦ ?_⟩,
    ⟨.mk (f'.restrictScalars k) fun h ↦ LinearMap.ext fun w ↦ ?_⟩⟩
  · simpa [hV, hV'] using f.map_smul (MonoidAlgebra.single g 1) v
  · simpa [hW, hW'] using f'.map_smul (MonoidAlgebra.single h 1) w

/-- **Every irreducible representation of a product of monoids is an external tensor product.**
Over an algebraically closed field `k`, a finite-dimensional irreducible representation `τ` of
`G × H` is equivalent to `ρ ⊠ σ` for finite-dimensional irreducible representations `ρ` of `G` and
`σ` of `H`, whose carriers lie in the universe of the carrier of `τ`. The factors are unique up to
equivalence (`Representation.nonempty_equiv_externalTensor_iff`). -/
theorem exists_isIrreducible_nonempty_equiv_externalTensor [IsAlgClosed k] {U : Type u}
    [AddCommGroup U] [Module k U] [FiniteDimensional k U] (τ : Representation k (G × H) U)
    [τ.IsIrreducible] :
    ∃ (V W : Type u) (_ : AddCommGroup V) (_ : Module k V) (_ : AddCommGroup W) (_ : Module k W)
      (ρ : Representation k G V) (σ : Representation k H W),
      FiniteDimensional k V ∧ FiniteDimensional k W ∧ ρ.IsIrreducible ∧ σ.IsIrreducible ∧
        Nonempty (τ.Equiv (ρ.externalTensor σ)) := by
  -- `U` is a simple module over `k[G] ⊗[k] k[H]`.
  let _ : Module (k[G] ⊗[k] k[H]) U := Module.compHom U (tensorAlgHom τ).toRingHom
  -- `Module.compHom` acts through the algebra map; this equation holds by definition.
  have hU (t : k[G] ⊗[k] k[H]) (u : U) : t • u = tensorAlgHom τ t u := rfl
  have : IsScalarTower k (k[G] ⊗[k] k[H]) U := ⟨fun c t u ↦ by simp [hU]⟩
  have : IsSimpleModule (k[G] ⊗[k] k[H]) U := by
    have : Nontrivial U := IsIrreducible.nontrivial ‹_›
    refine { eq_bot_or_eq_top := fun N ↦ ?_ }
    -- A submodule is a subrepresentation, since `(g, h)` acts as `single g 1 ⊗ single h 1`.
    let S : Subrepresentation τ :=
      ⟨N.restrictScalars k, fun p u hu ↦ by
        simpa [hU, tensorAlgHom_single_tmul_single] using
          N.smul_mem (MonoidAlgebra.single p.1 1 ⊗ₜ MonoidAlgebra.single p.2 1) hu⟩
    refine (eq_bot_or_eq_top S).imp (fun h ↦ ?_) (fun h ↦ ?_)
    · exact (Submodule.restrictScalars_eq_bot_iff k (k[G] ⊗[k] k[H]) U).1
        ((congrArg Subrepresentation.toSubmodule h).trans Subrepresentation.toSubmodule_bot)
    · exact (Submodule.restrictScalars_eq_top_iff k (k[G] ⊗[k] k[H]) U).1
        ((congrArg Subrepresentation.toSubmodule h).trans Subrepresentation.toSubmodule_top)
  -- Flath's factorization of the simple module `U`.
  obtain ⟨V, W, _, _, _, _, _, _, _, _, hV, hW, _, _, e, he⟩ :=
    TauCeti.exists_tensorProduct_equiv_of_isSimpleModule k k[G] k[H] U
  refine ⟨V, W, _, _, _, _, ofModule' V, ofModule' W, ‹_›, ‹_›,
    (isIrreducible_ofModule'_iff V).2 hV, (isIrreducible_ofModule'_iff W).2 hW,
    ⟨(Equiv.mk e fun p ↦ LinearMap.ext fun x ↦ ?_).symm⟩⟩
  have := he (MonoidAlgebra.single p.1 1 ⊗ₜ MonoidAlgebra.single p.2 1) x
  rwa [tensorPairAction_eq_tensorAlgHom, tensorAlgHom_single_tmul_single, hU,
    tensorAlgHom_single_tmul_single] at this

end Representation

namespace FDRep

open CategoryTheory

universe u v w

variable {k : Type u} {G : Type v} {H : Type w} [Field k] [Monoid G] [Monoid H]

/-- **Every simple representation of a product of monoids is an external tensor product of simple
representations**, over an algebraically closed field. The factors are unique up to
isomorphism. -/
theorem externalTensor_classification [IsAlgClosed k] (X : FDRep k (G × H)) [Simple X] :
    ∃ (V : FDRep k G) (W : FDRep k H), Simple V ∧ Simple W ∧
      Nonempty (X ≅ FDRep.of (Representation.externalTensor V.ρ W.ρ)) ∧
      ∀ (V' : FDRep k G) (W' : FDRep k H), Simple V' → Simple W' →
        Nonempty (X ≅ FDRep.of (Representation.externalTensor V'.ρ W'.ρ)) →
          Nonempty (V ≅ V') ∧ Nonempty (W ≅ W') := by
  have := isIrreducible_of_simple X
  obtain ⟨V, W, _, _, _, _, ρ, σ, _, _, hρ, hσ, ⟨e⟩⟩ :=
    Representation.exists_isIrreducible_nonempty_equiv_externalTensor X.ρ
  let V₀ := FDRep.of ρ
  let W₀ := FDRep.of σ
  have hV₀ : Simple V₀ := (simple_iff_isIrreducible V₀).mpr (by simpa only [V₀, of_ρ'] using hρ)
  have hW₀ : Simple W₀ := (simple_iff_isIrreducible W₀).mpr (by simpa only [W₀, of_ρ'] using hσ)
  have i : X ≅ FDRep.of (Representation.externalTensor V₀.ρ W₀.ρ) :=
    e.toLinearEquiv.toFDRepIso fun g x ↦ LinearMap.congr_fun (e.isIntertwining' g) x
  refine ⟨V₀, W₀, hV₀, hW₀, ⟨i⟩, fun V' W' hV' hW' ⟨j⟩ ↦ ?_⟩
  have := isIrreducible_of_simple V₀
  have := isIrreducible_of_simple W₀
  have := isIrreducible_of_simple V'
  have := isIrreducible_of_simple W'
  obtain ⟨⟨f⟩, ⟨g⟩⟩ :=
    (Representation.nonempty_equiv_externalTensor_iff V₀.ρ W₀.ρ V'.ρ W'.ρ).mp
      ⟨isoToEquiv (i.symm ≪≫ j)⟩
  exact ⟨⟨f.toLinearEquiv.toFDRepIso fun a x ↦ LinearMap.congr_fun (f.isIntertwining' a) x⟩,
    ⟨g.toLinearEquiv.toFDRepIso fun a x ↦ LinearMap.congr_fun (g.isIntertwining' a) x⟩⟩

end FDRep
