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

A differential commuting with a group representation induces a differential commuting with its
finite wreath tensor representation and hence with tensor induction along a subgroup. In
characteristic two the induced differential squares to zero. If the original action preserves
a grading, both actions preserve each total-degree piece `PiTensorProduct.degreePiece`.

These identities supply the permutation-compatible differential for tensor induction of
complexes. The ground ring need not have characteristic two for equivariance or preservation of
degree; that hypothesis enters only the square-zero law without Koszul signs.
Over a commutative ring of characteristic two these restrictions assemble into cochain
complexes of representations, with terms the total-degree tensor pieces.

## Main definitions and lemmas

* `TauCeti.wreathTensorDifferential d ι`: the equivariant
  differential on a finite tensor power.
* `TauCeti.tensorInducedDifferential d s`: its restriction along
  a transversal's monomial map.
* `TauCeti.wreathTensor_mem_degreePiece ρ ι`: preservation of total degree by
  the wreath action.
* `TauCeti.tensorInducedRepresentation_mem_degreePiece U s τ`: preservation of total
  degree by tensor induction.
* `TauCeti.wreathTensorCochainComplex`: the total-degree complex with its wreath action.
* `TauCeti.tensorInducedCochainComplex`: its restriction along the monomial homomorphism.

Open `TauCeti` and write `wreathTensorDifferential d ι` or `tensorInducedDifferential d s`
to construct the differentials. The action lemmas likewise take their representation or
subgroup as an explicit argument.

## References

* L. Evens, "A generalization of the transfer map in the cohomology of groups",
  *Transactions of the American Mathematical Society* 108 (1963), §§2–5.
-/

public section

open scoped TensorProduct

universe u v w x

namespace TauCeti

variable {R : Type u} [CommSemiring R] {D : Type v} [Group D]
  {M : Type w} [AddCommMonoid M] [Module R M] {ρ : Representation R D M}
  (d : ρ.IntertwiningMap ρ) (ι : Type x) [Fintype ι]

/-- The finite tensor differential, bundled as an endomorphism of the wreath tensor
representation. It applies the original endomorphism in one factor at a time and sums. -/
noncomputable def wreathTensorDifferential :
    (ρ.wreathTensor ι).IntertwiningMap (ρ.wreathTensor ι) where
  toLinearMap := TauCeti.PiTensorProduct.differential (fun _ : ι ↦ d.toLinearMap)
  isIntertwining' a := by
    rw [wreathTensor_apply, ← LinearMap.comp_assoc,
      TauCeti.PiTensorProduct.differential_comp_map _ _ _ (fun i ↦ d.isIntertwining' (a.left i)),
      LinearMap.comp_assoc,
      TauCeti.PiTensorProduct.differential_comp_reindex a.right (fun _ ↦ d.toLinearMap),
      LinearMap.comp_assoc]

/-- The underlying map of the wreath tensor differential is the finite tensor differential. -/
@[simp]
theorem wreathTensorDifferential_toLinearMap :
    (wreathTensorDifferential d ι).toLinearMap =
      TauCeti.PiTensorProduct.differential (fun _ : ι ↦ d.toLinearMap) :=
  (rfl)

/-- The wreath tensor differential replaces one pure-tensor factor at a time. -/
@[simp]
theorem wreathTensorDifferential_apply_tprod [DecidableEq ι] (x : ι → M) :
    wreathTensorDifferential d ι (_root_.PiTensorProduct.tprod R x) =
      ∑ i, _root_.PiTensorProduct.tprod R (Function.update x i (d (x i))) := by
  exact TauCeti.PiTensorProduct.differential_tprod (fun _ ↦ d.toLinearMap) x

/-- The induced differential squares to zero in characteristic two. -/
theorem wreathTensorDifferential_comp_self [CharP R 2]
    (hd : d.comp d = 0) :
    (wreathTensorDifferential d ι).comp (wreathTensorDifferential d ι) = 0 := by
  apply Representation.IntertwiningMap.ext
  exact TauCeti.PiTensorProduct.differential_comp_self _
    (fun _ ↦ congrArg Representation.IntertwiningMap.toLinearMap hd)

variable {G : Type*} [Group G] {U : Subgroup G}
  {τ : Representation R U M}

/-- The finite tensor differential on the tensor-induced representation, obtained by
restricting the wreath tensor differential along the monomial homomorphism. -/
noncomputable def tensorInducedDifferential (d : τ.IntertwiningMap τ)
    (s : U.LeftTransversal) [Fintype (G ⧸ U)] :
    (U.tensorInducedRepresentation s τ).IntertwiningMap
      (U.tensorInducedRepresentation s τ) where
  toLinearMap := (wreathTensorDifferential d (G ⧸ U)).toLinearMap
  isIntertwining' g := by
    apply LinearMap.ext
    intro z
    simp only [LinearMap.comp_apply, Subgroup.tensorInducedRepresentation_apply]
    exact LinearMap.congr_fun
      ((wreathTensorDifferential d (G ⧸ U)).isIntertwining' (U.monomialHom s g)) z

/-- Tensor induction uses the finite tensor differential on the coset-indexed tensor power. -/
@[simp]
theorem tensorInducedDifferential_toLinearMap (d : τ.IntertwiningMap τ)
    (s : U.LeftTransversal) [Fintype (G ⧸ U)] :
    (tensorInducedDifferential d s).toLinearMap =
      TauCeti.PiTensorProduct.differential (fun _ : G ⧸ U ↦ d.toLinearMap) :=
  (rfl)

/-- The tensor-induced differential replaces one coset-indexed pure-tensor factor at a time. -/
@[simp]
theorem tensorInducedDifferential_apply_tprod (d : τ.IntertwiningMap τ)
    (s : U.LeftTransversal) [Fintype (G ⧸ U)] [DecidableEq (G ⧸ U)] (x : G ⧸ U → M) :
    tensorInducedDifferential d s (_root_.PiTensorProduct.tprod R x) =
      ∑ i, _root_.PiTensorProduct.tprod R (Function.update x i (d (x i))) :=
  wreathTensorDifferential_apply_tprod d (G ⧸ U) x

/-- The tensor-induced differential squares to zero in characteristic two. -/
theorem tensorInducedDifferential_comp_self [CharP R 2] (d : τ.IntertwiningMap τ)
    (s : U.LeftTransversal) [Fintype (G ⧸ U)] (hd : d.comp d = 0) :
    (tensorInducedDifferential d s).comp (tensorInducedDifferential d s) = 0 := by
  apply Representation.IntertwiningMap.ext
  simpa only [Representation.IntertwiningMap.comp_toLinearMap,
    Representation.IntertwiningMap.zero_toLinearMap, tensorInducedDifferential_toLinearMap,
    wreathTensorDifferential_toLinearMap] using
    congrArg Representation.IntertwiningMap.toLinearMap
      (wreathTensorDifferential_comp_self d (G ⧸ U) hd)

end TauCeti

namespace TauCeti

variable {R : Type u} [CommSemiring R] {D : Type v} [Group D]
  {M : Type w} [AddCommMonoid M] [Module R M] (ρ : Representation R D M)
  (ι : Type x) [Fintype ι]

/-- A grading-preserving action gives a wreath tensor action preserving total tensor degree. -/
theorem wreathTensor_mem_degreePiece (ℳ : ℤ → Submodule R M)
    (hρ : ∀ g, LinearMap.IsHomogeneous (ρ g) ℳ ℳ 0)
    (a : WreathProduct D ι) {n : ℤ} {z : ⨂[R] _ : ι, M}
    (hz : z ∈ PiTensorProduct.degreePiece (fun _ : ι ↦ ℳ) n) :
    ρ.wreathTensor ι a z ∈ PiTensorProduct.degreePiece (fun _ : ι ↦ ℳ) n := by
  rw [wreathTensor_apply, LinearMap.comp_apply]
  exact PiTensorProduct.map_mem_degreePiece _ _ _ (fun i ↦ hρ (a.left i))
    (PiTensorProduct.reindex_mem_degreePiece a.right (fun _ ↦ ℳ) hz)

end TauCeti

namespace TauCeti

variable {R : Type u} [CommSemiring R] {M : Type w} [AddCommMonoid M] [Module R M]

/-- A grading-preserving subgroup action gives a tensor-induced action preserving total degree. -/
theorem tensorInducedRepresentation_mem_degreePiece {G : Type v} [Group G]
    (U : Subgroup G) (s : U.LeftTransversal) [Fintype (G ⧸ U)]
    (τ : Representation R U M) (ℳ : ℤ → Submodule R M)
    (hτ : ∀ g, LinearMap.IsHomogeneous (τ g) ℳ ℳ 0)
    (g : G) {n : ℤ} {z : ⨂[R] _ : G ⧸ U, M}
    (hz : z ∈ PiTensorProduct.degreePiece (fun _ : G ⧸ U ↦ ℳ) n) :
    U.tensorInducedRepresentation s τ g z ∈
      PiTensorProduct.degreePiece (fun _ : G ⧸ U ↦ ℳ) n := by
  rw [Subgroup.tensorInducedRepresentation_apply]
  exact wreathTensor_mem_degreePiece τ (G ⧸ U) ℳ hτ
    (U.monomialHom s g) hz

end TauCeti

namespace TauCeti

open CategoryTheory

section Complex

variable {R : Type u} [CommRing R] [CharP R 2] {D : Type v} [Group D]
  {M : Type w} [AddCommGroup M] [Module R M] {ρ : Representation R D M}
  (ℳ : ℤ → Submodule R M) (hρ : ∀ g, LinearMap.IsHomogeneous (ρ g) ℳ ℳ 0)
  (d : ρ.IntertwiningMap ρ) (hdeg : LinearMap.IsHomogeneous d.toLinearMap ℳ ℳ 1)
  (hd : d.comp d = 0) (ι : Type x) [Fintype ι]

/-- The total-degree tensor complex with its wreath-product action. Its differential is the
finite tensor differential restricted to each degree piece. -/
noncomputable def wreathTensorCochainComplex :
    CochainComplex (Rep.{max u w x} R (WreathProduct D ι)) ℤ :=
  CochainComplex.of (fun n ↦ Rep.of ((ρ.wreathTensor ι).subrepresentation
    (PiTensorProduct.degreePiece (fun _ : ι ↦ ℳ) n)
    (fun a _ hz ↦ wreathTensor_mem_degreePiece ρ ι ℳ hρ a hz)))
    (fun n ↦ Rep.ofHom {
      toLinearMap := (PiTensorProduct.differential (fun _ : ι ↦ d.toLinearMap)).restrict
        (p := PiTensorProduct.degreePiece (fun _ : ι ↦ ℳ) n)
        (q := PiTensorProduct.degreePiece (fun _ : ι ↦ ℳ) (n + 1))
        (fun _ hz ↦ (PiTensorProduct.isHomogeneous_differential
          (fun _ : ι ↦ ℳ) (fun _ ↦ d.toLinearMap) (fun _ ↦ hdeg)).map_mem hz)
      isIntertwining' a := by
        ext z
        exact LinearMap.congr_fun ((wreathTensorDifferential d ι).isIntertwining' a) z })
    (fun n ↦ by
      apply Rep.hom_ext
      apply Representation.IntertwiningMap.ext
      apply LinearMap.ext
      intro z
      apply Subtype.ext
      exact LinearMap.congr_fun
        (congrArg Representation.IntertwiningMap.toLinearMap
          (wreathTensorDifferential_comp_self d ι hd)) z)

/-- A term of the wreath tensor complex is the wreath action restricted to the total-degree
tensor piece. -/
@[simp]
theorem wreathTensorCochainComplex_X (n : ℤ) :
    (wreathTensorCochainComplex ℳ hρ d hdeg hd ι).X n =
      Rep.of ((ρ.wreathTensor ι).subrepresentation
        (PiTensorProduct.degreePiece (fun _ : ι ↦ ℳ) n)
        (fun a _ hz ↦ wreathTensor_mem_degreePiece ρ ι ℳ hρ a hz)) :=
  (rfl)

/-- Under the term identifications, the complex differential is the restricted finite tensor
differential as a linear map. This is an explicit rewrite lemma, since simplification expands
the composite morphism before this formula applies. -/
theorem wreathTensorCochainComplex_d (n : ℤ) :
    (eqToHom (wreathTensorCochainComplex_X ℳ hρ d hdeg hd ι n).symm ≫
      (wreathTensorCochainComplex ℳ hρ d hdeg hd ι).d n (n + 1) ≫
      eqToHom (wreathTensorCochainComplex_X ℳ hρ d hdeg hd ι (n + 1))).hom.toLinearMap =
      (PiTensorProduct.differential (fun _ : ι ↦ d.toLinearMap)).restrict
        (p := PiTensorProduct.degreePiece (fun _ : ι ↦ ℳ) n)
        (q := PiTensorProduct.degreePiece (fun _ : ι ↦ ℳ) (n + 1))
        (fun _ hz ↦ (PiTensorProduct.isHomogeneous_differential
          (fun _ : ι ↦ ℳ) (fun _ ↦ d.toLinearMap) (fun _ ↦ hdeg)).map_mem hz) := by
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
