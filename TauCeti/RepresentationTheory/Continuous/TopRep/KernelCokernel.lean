/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Continuous.TopRep
public import TauCeti.RepresentationTheory.Continuous.Subrepresentation

/-!
# Kernels and cokernels in `TopRep k G`

For a morphism `f : A ⟶ B` of continuous representations, the kernel of the underlying linear
map is an invariant submodule of `A` and the range is an invariant submodule of `B`. With the
subspace and quotient topologies they carry continuous representations
(`ContRepresentation.subrepresentation`, `ContRepresentation.quotient`), and they are the kernel
and the cokernel of `f` in `TopRep k G`, as for `TopModuleCat.ker` and `TopModuleCat.coker` in
the category of topological modules.

## Main definitions

* `TopRep.ker`, `TopRep.kerι`: the kernel of a morphism, with its inclusion.
* `TopRep.coker`, `TopRep.cokerπ`: the cokernel of a morphism, with its projection.

## Main results

* `TopRep.isLimitKer`: `TopRep.kerι f` is a kernel of `f`.
* `TopRep.isColimitCoker`: `TopRep.cokerπ f` is a cokernel of `f`.
* `TopRep.exact_kerι`, `TopRep.exact_cokerπ`: the underlying maps of `kerι f, f` and of
  `f, cokerπ f` are exact.
-/

public section

namespace TopRep

open CategoryTheory Limits

variable {k G : Type*} [Ring k] [TopologicalSpace k] [Monoid G] {A B : TopRep k G} (f : A ⟶ B)

/-- The kernel of a morphism of continuous representations: the kernel of the underlying linear
map with the subspace topology and the restricted action. -/
abbrev ker : TopRep k G :=
  .of f.hom.kerRepresentation

/-- The inclusion of the kernel of a morphism. -/
def kerι : ker f ⟶ A :=
  ofHom
    { toContinuousLinearMap := (f.hom.ker).subtypeL
      isIntertwining' _ := by ext; simp }

-- `simp` reduces the `abbrev` carriers `(ker f).V` and `(coker f).V` in implicit type arguments
-- before it looks a term up, so the evaluation lemmas below state their left-hand sides through
-- `dsimp% only`, as in #8315.
/-- The inclusion of the kernel sends a vector to the same vector of `A`. -/
@[simp]
theorem kerι_apply (a : ker f) : dsimp% only ((kerι f).hom a) = a.1 :=
  (rfl)

/-- The inclusion of the kernel is injective. -/
theorem kerι_injective : Function.Injective (kerι f).hom :=
  Subtype.val_injective

/-- The inclusion of the kernel of `f` is exact at `A` with `f`. -/
theorem exact_kerι : Function.Exact (kerι f).hom f.hom :=
  LinearMap.exact_subtype_ker_map (f.hom : A →ₗ[k] B)

/-- The inclusion of the kernel of `f` composed with `f` is zero. -/
@[reassoc (attr := simp)]
theorem kerι_comp : kerι f ≫ f = 0 := by
  ext a
  exact LinearMap.mem_ker.1 a.2

/-- `TopRep.kerι f` is a kernel of `f` in `TopRep k G`. -/
def isLimitKer : IsLimit (KernelFork.ofι (kerι f) (kerι_comp f)) :=
  KernelFork.IsLimit.ofι _ _
    (fun {X} e he ↦ ofHom
      { toContinuousLinearMap := e.hom.toContinuousLinearMap.codRestrict _ fun x ↦
          congr($he x)
        isIntertwining' g := by
          ext x
          simpa [ContIntertwiningMap.toContinuousLinearMap_apply] using hom_comm_apply e g x })
    (fun _ _ ↦ rfl)
    (fun e he m hm ↦ by
      ext x
      exact congr($hm x))

/-- The cokernel of a morphism of continuous representations: the quotient by the range of the
underlying linear map, with the quotient topology and the descended action. -/
abbrev coker : TopRep k G :=
  .of f.hom.cokerRepresentation

/-- The projection onto the cokernel of a morphism. -/
def cokerπ : B ⟶ coker f :=
  ofHom
    { toContinuousLinearMap := (f.hom.range).mkQL
      isIntertwining' _ := by ext; simp }

/-- The projection onto the cokernel sends a vector to its class. -/
@[simp]
theorem cokerπ_apply (b : B) : dsimp% only ((cokerπ f).hom b) = Submodule.Quotient.mk b :=
  (rfl)

/-- The projection onto the cokernel is surjective. -/
theorem cokerπ_surjective : Function.Surjective (cokerπ f).hom :=
  Submodule.mkQ_surjective _

/-- `f` is exact at `B` with the projection onto its cokernel. -/
theorem exact_cokerπ : Function.Exact f.hom (cokerπ f).hom :=
  LinearMap.exact_map_mkQ_range (f.hom : A →ₗ[k] B)

/-- `f` composed with the projection onto its cokernel is zero. -/
@[reassoc (attr := simp)]
theorem comp_cokerπ : f ≫ cokerπ f = 0 := by
  ext a
  exact (Submodule.Quotient.mk_eq_zero _).2 ⟨a, rfl⟩

/-- `TopRep.cokerπ f` is a cokernel of `f` in `TopRep k G`. -/
def isColimitCoker : IsColimit (CokernelCofork.ofπ (cokerπ f) (comp_cokerπ f)) :=
  CokernelCofork.IsColimit.ofπ _ _
    (fun {X} e he ↦ ofHom
      { toContinuousLinearMap := Submodule.liftQL _ e.hom.toContinuousLinearMap <| by
          rintro _ ⟨a, rfl⟩
          exact congr($he a)
        isIntertwining' g := by
          ext b
          obtain ⟨b, rfl⟩ := Submodule.mkQ_surjective _ b
          simpa [ContIntertwiningMap.toContinuousLinearMap_apply] using hom_comm_apply e g b })
    (fun _ _ ↦ rfl)
    (fun e he m hm ↦ by
      ext b
      induction b using Submodule.Quotient.induction_on
      exact congr($hm _))

section NatCastSMul

variable {k G : Type*} [CommRing k] [TopologicalSpace k] [Monoid G] (A : TopRep k G) (ℓ : ℕ)

/-- Multiplication by the natural number `ℓ` on a continuous representation acts on the carrier as
`a ↦ ℓ • a`. -/
@[simp]
theorem natCast_smul_id_apply (a : A.V) : ((ℓ : k) • 𝟙 A : A ⟶ A).hom a = ℓ • a := by
  rw [hom_smul, ContIntertwiningMap.smul_apply, Nat.cast_smul_eq_nsmul]
  -- the underlying map of `𝟙 A` is the identity of the carrier
  rfl

/-- The `ℓ`-torsion of a finite representation is strictly smaller than the representation when `ℓ`
does not kill it. -/
theorem card_ker_natCast_smul_id_lt [Finite A.V] (x : A.V) (hx : ℓ • x ≠ 0) :
    Nat.card (ker ((ℓ : k) • 𝟙 A)).V < Nat.card A.V := by
  have : Fintype A.V := Fintype.ofFinite _
  have hι := kerι_injective ((ℓ : k) • 𝟙 A)
  have : Finite (ker ((ℓ : k) • 𝟙 A)).V := .of_injective _ hι
  have : Fintype (ker ((ℓ : k) • 𝟙 A)).V := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  refine Fintype.card_lt_of_injective_not_surjective _ hι fun hsurj ↦ hx ?_
  obtain ⟨z, hz⟩ := hsurj x
  have hz' := z.2
  rw [LinearMap.mem_ker] at hz'
  rw [← hz, ← natCast_smul_id_apply, kerι_apply]
  exact hz'

/-- The quotient of a finite representation by its `ℓ`-torsion is strictly smaller than the
representation when a nonzero vector is killed by `ℓ`. -/
theorem card_coker_kerι_natCast_smul_id_lt [Finite A.V] (y : A.V) (hy0 : y ≠ 0) (hy : ℓ • y = 0) :
    Nat.card (coker (kerι ((ℓ : k) • 𝟙 A))).V < Nat.card A.V := by
  have : Fintype A.V := Fintype.ofFinite _
  set f : A ⟶ A := (ℓ : k) • 𝟙 A
  set ι := kerι f
  have hπ : Function.Surjective (cokerπ ι).hom := cokerπ_surjective ι
  have hιπ : Function.Exact ι.hom (cokerπ ι).hom := exact_cokerπ ι
  have : Finite (coker ι).V := .of_surjective _ hπ
  have : Fintype (coker ι).V := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  refine Fintype.card_lt_of_surjective_not_injective _ hπ fun hinj ↦ ?_
  have hyker : y ∈ LinearMap.ker (f.hom : A.V →ₗ[k] A.V) := by
    rw [LinearMap.mem_ker]
    exact (natCast_smul_id_apply A ℓ y).trans hy
  have hyι : (cokerπ ι).hom y = (cokerπ ι).hom 0 := by
    rw [map_zero]
    exact (hιπ y).2 ⟨⟨y, hyker⟩, kerι_apply f _⟩
  exact hy0 (hinj hyι)

end NatCastSMul

end TopRep
