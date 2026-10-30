/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Orthogonal.TypeB.Basic
public import TauCeti.RepresentationTheory.Spin.Polarization.Split.Even
public import TauCeti.RepresentationTheory.Spin.Polarization.Split.Odd
public import TauCeti.RepresentationTheory.Spin.Polarization.TypeB.Representation
public import TauCeti.RepresentationTheory.Spin.Polarization.TypeD.Representation

/-!
# Restricting the type-B spin representation to type D

Let `V₁ = W₁ ⊕ W₁'` be a quadratic space of dimension `2l` with an even polarization, and let
`V₂ = W₂ ⊕ W₂' ⊕ L` be a quadratic space of dimension `2l + 1` with an odd polarization whose
remainder `L` contains a vector `z` with `Q₂ z = 1`. An isometric embedding `f : V₁ → V₂`
carrying a basis `b₁` of `W₁` to a basis `b₂` of `W₂` and `W₁'` into `W₂'` identifies the
hyperbolic basis of `V₁` with the part of the odd hyperbolic basis of `V₂` orthogonal to `z`.
Through these bases, `so(2l)` sits inside `so(2l + 1)` as the matrices with vanishing anisotropic
row and column, `LieAlgebra.Orthogonal.typeB.ofTypeD`.

This file proves that the type-`B` spin representation of `so(2l + 1)` on `⋀·W₂`, restricted
along this inclusion, is the type-`D` spin representation of `so(2l)` on `⋀·W₁`, transported by
the algebra isomorphism `⋀·W₁ ≃ ⋀·W₂` induced by `b₁ ↦ b₂`. The type-`D` spin module splits into
the half-spin modules `S⁺ = ⋀ᵉᵛᵉⁿ W₁` and `S⁻ = ⋀ᵒᵈᵈ W₁`
(`TauCeti.isCompl_spinPlus_spinMinus`, `TauCeti.SpinPolarizationData.typeDSpinPlusLieRep` and
`TauCeti.SpinPolarizationData.typeDSpinMinusLieRep`), so the restriction of the spin module of
`so(2l + 1)` to `so(2l)` is `S⁺ ⊕ S⁻`.

The comparison has two halves.

* The Fock actions are natural: the Clifford algebra map induced by `f` intertwines the two
  Fock actions through `⋀·W₁ → ⋀·W₂` (`spinAction_map_comp_exteriorAlgebraMap`). On a vector of
  `W₁` both sides are exterior multiplication, and on a vector of `W₁'` both are contraction,
  because `f` preserves the polar pairing.
* The quadratic elements match: `f` carries the quadratic element of a type-`D` matrix `A` to
  the quadratic element of its zero extension (`map_typeDQuadraticEquiv`). Both are quadratic,
  so it suffices to compare their commutators with the generators; they agree on the image of
  `f`, and both commute with `z`, which is orthogonal to that image.

The standard split spaces `TauCeti.SplitEvenSpace K n ⊆ TauCeti.SplitOddSpace K n` satisfy these
hypotheses, giving the concrete instance
`splitOddPolarization_typeBSpinLieRep_ofTypeD_comp_exteriorAlgebraMap`.

## Main results

* `TauCeti.SpinPolarizationData.map_typeDQuadraticEquiv`: the embedding carries type-`D`
  quadratic elements to the type-`B` quadratic elements of the zero-extended matrices.
* `TauCeti.SpinPolarizationData.typeBSpinLieRep_ofTypeD_comp_exteriorAlgebraMap`: **the
  restriction of the type-`B` spin representation to `so(2l)` is the type-`D` spin
  representation**.
* `TauCeti.splitOddPolarization_typeBSpinLieRep_ofTypeD_comp_exteriorAlgebraMap`: the same
  statement for the standard split spaces.

## References

* C. Chevalley, *The Algebraic Theory of Spinors*, Chapter II.
* W. Fulton and J. Harris, *Representation Theory: A First Course* (1991), Section 20.2.
-/

public section

open CliffordAlgebra

namespace TauCeti

namespace SpinPolarizationData

universe u v₁ v₂ w

attribute [local instance 100] LieRing.ofAssociativeRing

/-! ### The type-`D` matrices inside the type-`B` matrices -/

section TypeB

variable {K : Type u} [Field K] {V₁ : Type v₁} [AddCommGroup V₁] [Module K V₁]
  {V₂ : Type v₂} [AddCommGroup V₂] [Module K V₂]
  {Q₁ : QuadraticForm K V₁} {Q₂ : QuadraticForm K V₂}
  (P₁ : SpinPolarizationData Q₁) (P₂ : SpinPolarizationData Q₂)
  {ι : Type w} (b₁ : Module.Basis ι K P₁.W) (b₂ : Module.Basis ι K P₂.W)
  (z : P₂.line) (hz : Q₂ (z : V₂) = 1) {f : Q₁ →qᵢ Q₂}

variable [Fintype ι] [DecidableEq ι]

/-- The hyperbolic basis of the even space is carried to the part of the odd hyperbolic basis
orthogonal to the remainder vector. -/
private theorem apply_typeDBasis (hline : P₁.line = ⊥) (hb : ∀ i, f (b₁ i) = b₂ i)
    (hW' : ∀ y : P₁.W', f y ∈ P₂.W') (c : ι ⊕ ι) :
    f (P₁.typeDBasis b₁ hline c) = P₂.typeBBasis b₂ z hz (.inr c) := by
  rcases c with i | i
  · simp [hb]
  · simp [apply_dualVector P₁ P₂ b₁ b₂ hb hW']

variable [Invertible (2 : K)]

/-- **The embedding carries type-`D` quadratic elements to type-`B` quadratic elements.** The
Clifford algebra map induced by `f` sends the quadratic element of a type-`D` matrix `A` to the
quadratic element of its zero extension `LieAlgebra.Orthogonal.typeB.ofTypeD A`. -/
theorem map_typeDQuadraticEquiv (hline : P₁.line = ⊥) (hb : ∀ i, f (b₁ i) = b₂ i)
    (hW' : ∀ y : P₁.W', f y ∈ P₂.W') (A : LieAlgebra.Orthogonal.typeD ι K) :
    map f (P₁.typeDQuadraticEquiv b₁ hline A : CliffordAlgebra Q₁) =
      P₂.typeBQuadraticEquiv b₂ z hz (LieAlgebra.Orthogonal.typeB.ofTypeD A) := by
  set q := (P₁.typeDQuadraticEquiv b₁ hline A : CliffordAlgebra Q₁)
  have hq : q ∈ quadraticLieSubalgebra Q₁ := (P₁.typeDQuadraticEquiv b₁ hline A).property
  -- The image of a quadratic element commutes with the remainder vector, which is orthogonal to
  -- the image of `f`.
  have hz_comm : ⁅map f q, CliffordAlgebra.ι Q₂ (z : V₂)⁆ = 0 := by
    have key : (quadraticLieSubalgebra Q₁).toSubmodule ≤
        { carrier := {x | ⁅map f x, CliffordAlgebra.ι Q₂ (z : V₂)⁆ = 0}
          add_mem' := fun hx hy => by simp_all [add_lie]
          zero_mem' := by simp
          smul_mem' := fun r x hx => by simp_all [smul_lie] } :=
      quadraticLieSubalgebra_toSubmodule_le_of_bivector_mem Q₁ fun a c => by
        simp [map_bivector, bivector_lie_ι, polar_apply_line P₁ P₂ b₁ b₂ z hline hb hW']
    exact key hq
  -- The commutator with the image of `q` matches the zero-extended matrix on the odd hyperbolic
  -- basis: on the remainder vector both vanish, and on the image of `f` this is the type-`D`
  -- commutator formula transported by `f`.
  have hbasis : ∀ c, ⁅map f q, CliffordAlgebra.ι Q₂ (P₂.typeBBasis b₂ z hz c)⁆ =
      CliffordAlgebra.ι Q₂ (Matrix.toLinAlgEquiv (P₂.typeBBasis b₂ z hz)
        (LieAlgebra.Orthogonal.typeB.ofTypeD A) (P₂.typeBBasis b₂ z hz c)) := by
    rintro (⟨⟩ | c)
    · rw [typeBBasis_inl, hz_comm, ← typeBBasis_inl P₂ b₂ z hz (), Matrix.toLinAlgEquiv_self]
      simp [Fintype.sum_sum_type]
    · have hmap : map f ⁅q, CliffordAlgebra.ι Q₁ (P₁.typeDBasis b₁ hline c)⁆ =
          ⁅map f q, map f (CliffordAlgebra.ι Q₁ (P₁.typeDBasis b₁ hline c))⁆ :=
        (map f).toLieHom.map_lie _ _
      calc
        _ = map f ⁅q, CliffordAlgebra.ι Q₁ (P₁.typeDBasis b₁ hline c)⁆ := by
          simpa only [map_apply_ι, apply_typeDBasis P₁ P₂ b₁ b₂ z hz hline hb hW']
            using hmap.symm
        _ = CliffordAlgebra.ι Q₂
            (f (Matrix.toLinAlgEquiv (P₁.typeDBasis b₁ hline) A
              (P₁.typeDBasis b₁ hline c))) := by
          rw [P₁.typeDQuadraticEquiv_lie_ι, map_apply_ι]
        _ = _ := by
          simp only [Matrix.toLinAlgEquiv_self, map_sum, map_smul,
            apply_typeDBasis P₁ P₂ b₁ b₂ z hz hline hb hW']
          simp [Fintype.sum_sum_type]
  have h : LieAlgebra.ad K (CliffordAlgebra Q₂) (map f q) ∘ₗ CliffordAlgebra.ι Q₂ =
      CliffordAlgebra.ι Q₂ ∘ₗ Matrix.toLinAlgEquiv (P₂.typeBBasis b₂ z hz)
        (LieAlgebra.Orthogonal.typeB.ofTypeD A) :=
    (P₂.typeBBasis b₂ z hz).ext fun c => by
      simpa only [LinearMap.comp_apply, LieAlgebra.ad_apply] using hbasis c
  have _ : Module.Finite K V₂ := Module.Finite.of_basis (P₂.typeBBasis b₂ z hz)
  -- Both sides are quadratic, so it suffices to compare their commutators with generators.
  refine congrArg Subtype.val (quadraticLieSubalgebra_ext Q₂
    (P₂.nondegenerate ((isUnit_of_invertible (2 : K)).isSMulRegular K))
    (a := ⟨map f q, map_mem_quadraticLieSubalgebra f hq⟩) fun x => ?_)
  rw [P₂.typeBQuadraticEquiv_lie_ι]
  simpa only [LinearMap.comp_apply, LieAlgebra.ad_apply] using LinearMap.congr_fun h x

/-- **The restriction of the type-`B` spin representation to type `D`.** Under an isometric
embedding of an even polarization into an odd one that matches the bases `b₁` and `b₂` of the
first isotropic summands and carries the second isotropic summand into the second one, the action
of the zero extension of a type-`D` matrix `A` through the type-`B` spin representation on
`⋀·W₂` corresponds to the action of `A` through the type-`D` spin representation on `⋀·W₁`. The
two exterior algebras are compared by the algebra isomorphism induced by `b₁ ↦ b₂`. -/
theorem typeBSpinLieRep_ofTypeD_comp_exteriorAlgebraMap (hline : P₁.line = ⊥)
    (hb : ∀ i, f (b₁ i) = b₂ i) (hW' : ∀ y : P₁.W', f y ∈ P₂.W')
    (A : LieAlgebra.Orthogonal.typeD ι K) :
    P₂.typeBSpinLieRep b₂ z hz (LieAlgebra.Orthogonal.typeB.ofTypeD A) ∘ₗ
        (ExteriorAlgebra.map (b₁.equiv b₂ (Equiv.refl ι)).toLinearMap).toLinearMap =
      (ExteriorAlgebra.map (b₁.equiv b₂ (Equiv.refl ι)).toLinearMap).toLinearMap ∘ₗ
        P₁.typeDSpinLieRep b₁ hline A := by
  rw [typeBSpinLieRep_apply, typeDSpinLieRep_apply,
    ← map_typeDQuadraticEquiv P₁ P₂ b₁ b₂ z hz hline hb hW']
  exact spinAction_map_comp_exteriorAlgebraMap P₁ P₂ hline
    (apply_coe_eq_basisEquiv P₁ P₂ b₁ b₂ hb) hW' _

end TypeB

end SpinPolarizationData

/-! ### The standard split spaces -/

/-- **The restriction of the type-`B` spin representation to type `D`, for the standard split
spaces.** The split even space `TauCeti.SplitEvenSpace K n` is the hyperplane of the split odd
space `TauCeti.SplitOddSpace K n` where the last coordinate vanishes, and through this embedding
the type-`B` spin representation of the zero extension of a type-`D` matrix `A` is the type-`D`
spin representation of `A`, after identifying the two exterior algebras along the coordinate
bases. -/
theorem splitOddPolarization_typeBSpinLieRep_ofTypeD_comp_exteriorAlgebraMap {K : Type u}
    [Field K] [Invertible (2 : K)] (n : ℕ) (A : LieAlgebra.Orthogonal.typeD (Fin n) K) :
    (splitOddPolarization K n).typeBSpinLieRep (splitOddBasis K n) (splitOddRemainderOne K n)
        (splitOddForm_remainderOne K n) (LieAlgebra.Orthogonal.typeB.ofTypeD A) ∘ₗ
        (ExteriorAlgebra.map ((splitEvenBasis K n).equiv (splitOddBasis K n)
          (Equiv.refl _)).toLinearMap).toLinearMap =
      (ExteriorAlgebra.map ((splitEvenBasis K n).equiv (splitOddBasis K n)
          (Equiv.refl _)).toLinearMap).toLinearMap ∘ₗ
        (splitEvenPolarization K n).typeDSpinLieRep (splitEvenBasis K n)
          (splitEvenPolarization_line K n) A := by
  let f : splitEvenForm K n →qᵢ splitOddForm K n :=
    { LinearMap.inl K (SplitEvenSpace K n) K with map_app' := fun x => by simp }
  have hf (x : SplitEvenSpace K n) : f x = (x, 0) := (rfl)
  refine SpinPolarizationData.typeBSpinLieRep_ofTypeD_comp_exteriorAlgebraMap _ _ _ _ _ _
    (f := f) (splitEvenPolarization_line K n) (fun i => by simp [hf]) (fun y => ?_) A
  obtain ⟨y, hy⟩ := y
  simp only [splitEvenPolarization_W', Submodule.mem_prod, Submodule.mem_top,
    Submodule.mem_bot, true_and] at hy
  simp [hf, hy]

end TauCeti
