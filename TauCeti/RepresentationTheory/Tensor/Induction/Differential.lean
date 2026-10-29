/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.Additive
public import TauCeti.RepresentationTheory.Tensor.Induction.Basic
public import TauCeti.LinearAlgebra.PiTensorProduct.Complex

/-!
# Equivariant tensor differentials

A differential commuting with a group representation induces a slot-sum differential commuting
with its finite wreath tensor representation and hence with tensor induction along a subgroup.
In characteristic two the induced differential squares to zero. The existing
`Representation.isHomogeneous_wreathTensor` supplies preservation of total degree by the action.

These identities supply the permutation-compatible differential for tensor induction of
complexes. The ground ring need not have characteristic two for equivariance or preservation of
degree; that hypothesis enters only the square-zero law without Koszul signs.
Over a commutative ring of characteristic two these restrictions assemble into cochain
complexes of representations, with terms the total-degree tensor pieces.

## Main definitions and lemmas

* `Representation.IntertwiningMap.wreathTensorDifferential`: the equivariant slot-sum
  differential on a finite tensor power.
* `Representation.IntertwiningMap.tensorInducedSlotSum_comp_self`: the square-zero law for
  the existing tensor-induced slot sum.
* `TauCeti.wreathTensorCochainComplex`: the total-degree complex with its wreath action.
* `TauCeti.tensorInducedCochainComplex`: its restriction along the monomial homomorphism.

## References

* L. Evens, "A generalization of the transfer map in the cohomology of groups",
  *Transactions of the American Mathematical Society* 108 (1963), §§2–5.
-/

public section

open scoped TensorProduct

universe u v w x

namespace Representation.IntertwiningMap

variable {R : Type u} [CommSemiring R] {D : Type v} [Group D]
  {M : Type w} [AddCommMonoid M] [Module R M] {ρ : Representation R D M}
  (d : ρ.IntertwiningMap ρ) (ι : Type x) [Fintype ι] [DecidableEq ι]

/-- The slot sum, bundled as an endomorphism of the wreath tensor representation.
It applies the original endomorphism in one factor at a time and sums. -/
noncomputable def wreathTensorDifferential :
    (ρ.wreathTensor ι).IntertwiningMap (ρ.wreathTensor ι) where
  toLinearMap := TauCeti.PiTensorProduct.slotSum ι (fun _ ↦ d.toLinearMap)
  isIntertwining' := ρ.slotSum_comp_wreathTensor d.isIntertwining'

/-- The underlying map of the wreath tensor differential is the slot sum. -/
@[simp]
theorem wreathTensorDifferential_toLinearMap :
    (wreathTensorDifferential d ι).toLinearMap =
      TauCeti.PiTensorProduct.slotSum ι (fun _ ↦ d.toLinearMap) :=
  (rfl)

/-- The wreath tensor differential replaces one pure-tensor factor at a time. -/
@[simp]
theorem wreathTensorDifferential_apply_tprod (x : ι → M) :
    wreathTensorDifferential d ι (_root_.PiTensorProduct.tprod R x) =
      ∑ i, _root_.PiTensorProduct.tprod R (Function.update x i (d (x i))) :=
  TauCeti.PiTensorProduct.slotSum_tprod (fun _ ↦ d.toLinearMap) x

/-- The induced differential squares to zero in characteristic two. -/
theorem wreathTensorDifferential_comp_self [CharP R 2] (hd : d.comp d = 0) :
    (wreathTensorDifferential d ι).comp (wreathTensorDifferential d ι) = 0 := by
  apply Representation.IntertwiningMap.ext
  exact TauCeti.PiTensorProduct.slotSum_comp_slotSum
    (fun _ ↦ TauCeti.add_self_eq_zero_of_charTwo R)
    (fun _ ↦ congrArg Representation.IntertwiningMap.toLinearMap hd)

variable {G : Type*} [Group G] {U : Subgroup G} {τ : Representation R U M}

/-- The tensor-induced slot sum replaces one coset-indexed pure-tensor factor at a time. -/
@[simp]
theorem tensorInducedSlotSum_apply_tprod (d : τ.IntertwiningMap τ)
    (s : U.LeftTransversal) [Fintype (G ⧸ U)] [DecidableEq (G ⧸ U)] (x : G ⧸ U → M) :
    d.tensorInducedSlotSum s (_root_.PiTensorProduct.tprod R x) =
      ∑ i, _root_.PiTensorProduct.tprod R (Function.update x i (d (x i))) := by
  rw [← Representation.IntertwiningMap.toLinearMap_apply, tensorInducedSlotSum_toLinearMap]
  exact TauCeti.PiTensorProduct.slotSum_tprod _ x

/-- The tensor-induced slot sum squares to zero in characteristic two. -/
theorem tensorInducedSlotSum_comp_self [CharP R 2] (d : τ.IntertwiningMap τ)
    (s : U.LeftTransversal) [Fintype (G ⧸ U)] [DecidableEq (G ⧸ U)] (hd : d.comp d = 0) :
    (d.tensorInducedSlotSum s).comp (d.tensorInducedSlotSum s) = 0 := by
  apply Representation.IntertwiningMap.ext
  simp only [Representation.IntertwiningMap.comp_toLinearMap,
    Representation.IntertwiningMap.zero_toLinearMap, tensorInducedSlotSum_toLinearMap]
  exact TauCeti.PiTensorProduct.slotSum_comp_slotSum
    (fun _ ↦ TauCeti.add_self_eq_zero_of_charTwo R)
    (fun _ ↦ congrArg Representation.IntertwiningMap.toLinearMap hd)

end Representation.IntertwiningMap

namespace TauCeti

open CategoryTheory

section Complex

variable {R : Type u} [CommRing R] [CharP R 2] {D : Type v} [Group D]
  {M : Type w} [AddCommGroup M] [Module R M] {ρ : Representation R D M}
  (ℳ : ℤ → Submodule R M) (hρ : ∀ g, LinearMap.IsHomogeneous (ρ g) ℳ ℳ 0)
  (d : ρ.IntertwiningMap ρ) (hdeg : LinearMap.IsHomogeneous d.toLinearMap ℳ ℳ 1)
  (hd : d.comp d = 0) (ι : Type x) [Fintype ι]

open Classical in
/-- The total-degree tensor complex with its wreath-product action. Its differential is the
slot sum restricted to each degree piece. -/
noncomputable def wreathTensorCochainComplex :
    CochainComplex (Rep.{max u w x} R (WreathProduct D ι)) ℤ :=
  CochainComplex.of (fun n ↦ Rep.of ((ρ.wreathTensor ι).subrepresentation
    (PiTensorProduct.totalDegreePiece ι (fun _ ↦ ℳ) n)
    (fun a _ hz ↦ by simpa using (ρ.isHomogeneous_wreathTensor hρ a).map_mem hz)))
    (fun n ↦ Rep.ofHom {
      toLinearMap := (PiTensorProduct.slotSum ι (fun _ ↦ d.toLinearMap)).restrict
        (p := PiTensorProduct.totalDegreePiece ι (fun _ ↦ ℳ) n)
        (q := PiTensorProduct.totalDegreePiece ι (fun _ ↦ ℳ) (n + 1))
        (fun _ hz ↦ (PiTensorProduct.isHomogeneous_slotSum (fun _ : ι ↦ hdeg)).map_mem hz)
      isIntertwining' a := by
        ext z
        exact LinearMap.congr_fun ((d.wreathTensorDifferential ι).isIntertwining' a) z })
    (fun n ↦ by
      apply Rep.hom_ext
      apply Representation.IntertwiningMap.ext
      apply LinearMap.ext
      intro z
      apply Subtype.ext
      exact LinearMap.congr_fun
        (congrArg Representation.IntertwiningMap.toLinearMap
          (d.wreathTensorDifferential_comp_self ι hd)) z)

/-- A term of the wreath tensor complex is the wreath action restricted to the total-degree
tensor piece. -/
@[simp]
theorem wreathTensorCochainComplex_X (n : ℤ) :
    (wreathTensorCochainComplex ℳ hρ d hdeg hd ι).X n =
      Rep.of ((ρ.wreathTensor ι).subrepresentation
        (PiTensorProduct.totalDegreePiece ι (fun _ ↦ ℳ) n)
        (fun a _ hz ↦ by simpa using (ρ.isHomogeneous_wreathTensor hρ a).map_mem hz)) :=
  (rfl)

open Classical in
/-- Under the term identifications, the complex differential is the restricted slot sum
as a linear map. This is an explicit rewrite lemma, since simplification expands the composite
morphism before this formula applies. -/
theorem wreathTensorCochainComplex_d (n : ℤ) :
    (eqToHom (wreathTensorCochainComplex_X ℳ hρ d hdeg hd ι n).symm ≫
      (wreathTensorCochainComplex ℳ hρ d hdeg hd ι).d n (n + 1) ≫
      eqToHom (wreathTensorCochainComplex_X ℳ hρ d hdeg hd ι (n + 1))).hom.toLinearMap =
      (PiTensorProduct.slotSum ι (fun _ ↦ d.toLinearMap)).restrict
        (p := PiTensorProduct.totalDegreePiece ι (fun _ ↦ ℳ) n)
        (q := PiTensorProduct.totalDegreePiece ι (fun _ ↦ ℳ) (n + 1))
        (fun _ hz ↦ (PiTensorProduct.isHomogeneous_slotSum (fun _ : ι ↦ hdeg)).map_mem hz) := by
  -- The constructor has definitionally equal terms; eliminate their equality transports
  -- before applying its differential formula.
  have hn : wreathTensorCochainComplex_X ℳ hρ d hdeg hd ι n = rfl := Subsingleton.elim _ _
  have hn' : wreathTensorCochainComplex_X ℳ hρ d hdeg hd ι (n + 1) = rfl :=
    Subsingleton.elim _ _
  rw [hn, hn']
  unfold wreathTensorCochainComplex
  simp only [CochainComplex.of_d, eqToHom_refl, Category.id_comp, Category.comp_id,
    Rep.hom_ofHom]

/-- Forgetting the wreath action recovers the total-degree tensor complex of modules. -/
@[simp]
theorem wreathTensorCochainComplex_forget :
    ((forget₂ (Rep.{max u w x} R (WreathProduct D ι)) (ModuleCat R)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj (wreathTensorCochainComplex ℳ hρ d hdeg hd ι) =
      PiTensorProduct.cochainComplex (fun _ : ι ↦ ℳ) (fun _ ↦ d.toLinearMap)
        (fun _ ↦ hdeg) (fun _ ↦ by
          simpa only [Representation.IntertwiningMap.comp_toLinearMap,
            Representation.IntertwiningMap.zero_toLinearMap] using
            congrArg Representation.IntertwiningMap.toLinearMap hd) := by
  refine HomologicalComplex.ext ?_ ?_
  · funext n
    exact (PiTensorProduct.cochainComplex_X _ _ _ _ n).symm
  intro i j hij
  obtain rfl : i + 1 = j := hij
  rw [PiTensorProduct.cochainComplex_d]
  simp only [eqToHom_trans_assoc]
  congr 1
  unfold wreathTensorCochainComplex
  simp only [Functor.mapHomologicalComplex_obj_d, CochainComplex.of_d,
    Rep.forget₂_moduleCat_map, Rep.hom_ofHom]

variable {G : Type v} [Group G] {U : Subgroup G} {τ : Representation R U M}

/-- The tensor-induced total-degree complex, obtained by restricting the wreath tensor
complex along the transversal's monomial homomorphism. -/
noncomputable def tensorInducedCochainComplex (ℳ : ℤ → Submodule R M)
    (hτ : ∀ g, LinearMap.IsHomogeneous (τ g) ℳ ℳ 0) (d : τ.IntertwiningMap τ)
    (hdeg : LinearMap.IsHomogeneous d.toLinearMap ℳ ℳ 1) (hd : d.comp d = 0)
    (s : U.LeftTransversal) [Fintype (G ⧸ U)] :
    CochainComplex (Rep.{max u w v} R G) ℤ :=
  ((Rep.resFunctor (U.monomialHom s)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
    (wreathTensorCochainComplex ℳ hτ d hdeg hd (G ⧸ U))

/-- A tensor-induced term is the total-degree wreath tensor representation restricted along
the monomial homomorphism. -/
@[simp]
theorem tensorInducedCochainComplex_X (ℳ : ℤ → Submodule R M)
    (hτ : ∀ g, LinearMap.IsHomogeneous (τ g) ℳ ℳ 0) (d : τ.IntertwiningMap τ)
    (hdeg : LinearMap.IsHomogeneous d.toLinearMap ℳ ℳ 1) (hd : d.comp d = 0)
    (s : U.LeftTransversal) [Fintype (G ⧸ U)] (n : ℤ) :
    (tensorInducedCochainComplex ℳ hτ d hdeg hd s).X n =
      Rep.res (U.monomialHom s) ((wreathTensorCochainComplex ℳ hτ d hdeg hd (G ⧸ U)).X n) :=
  (rfl)

/-- The tensor-induced complex differential is the restriction of the wreath tensor complex
differential along the monomial homomorphism. -/
@[simp]
theorem tensorInducedCochainComplex_d (ℳ : ℤ → Submodule R M)
    (hτ : ∀ g, LinearMap.IsHomogeneous (τ g) ℳ ℳ 0) (d : τ.IntertwiningMap τ)
    (hdeg : LinearMap.IsHomogeneous d.toLinearMap ℳ ℳ 1) (hd : d.comp d = 0)
    (s : U.LeftTransversal) [Fintype (G ⧸ U)] (n m : ℤ) :
    (tensorInducedCochainComplex ℳ hτ d hdeg hd s).d n m =
      eqToHom (tensorInducedCochainComplex_X ℳ hτ d hdeg hd s n) ≫
        (Rep.resFunctor (U.monomialHom s)).map
          ((wreathTensorCochainComplex ℳ hτ d hdeg hd (G ⧸ U)).d n m) ≫
        eqToHom (tensorInducedCochainComplex_X ℳ hτ d hdeg hd s m).symm :=
  (rfl)

/-- Forgetting the tensor-induced action recovers the coset-indexed total-degree tensor
complex of modules. -/
@[simp]
theorem tensorInducedCochainComplex_forget (ℳ : ℤ → Submodule R M)
    (hτ : ∀ g, LinearMap.IsHomogeneous (τ g) ℳ ℳ 0) (d : τ.IntertwiningMap τ)
    (hdeg : LinearMap.IsHomogeneous d.toLinearMap ℳ ℳ 1) (hd : d.comp d = 0)
    (s : U.LeftTransversal) [Fintype (G ⧸ U)] :
    ((forget₂ (Rep.{max u w v} R G) (ModuleCat R)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj (tensorInducedCochainComplex ℳ hτ d hdeg hd s) =
      PiTensorProduct.cochainComplex (fun _ : G ⧸ U ↦ ℳ) (fun _ ↦ d.toLinearMap)
        (fun _ ↦ hdeg) (fun _ ↦ by
          simpa only [Representation.IntertwiningMap.comp_toLinearMap,
            Representation.IntertwiningMap.zero_toLinearMap] using
            congrArg Representation.IntertwiningMap.toLinearMap hd) := by
  unfold tensorInducedCochainComplex
  rw [← wreathTensorCochainComplex_forget ℳ hτ d hdeg hd (G ⧸ U)]
  -- Rep.resFunctor changes only the action: res and resMap retain the module and
  -- linear map. mapHomologicalComplex therefore has the same terms and differentials
  -- after forgetting either action.
  rfl

end Complex

end TauCeti
