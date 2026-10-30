/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.PiTensorProduct.Basis
public import Mathlib.LinearAlgebra.PiTensorProduct.DFinsupp
public import Mathlib.RingTheory.Finiteness.Projective

/-!
# The tensor product of hom modules is the hom module of the tensor products

Mathlib's `PiTensorProduct.piTensorHomMap` is the canonical comparison map

`⨂ᵢ (Mᵢ →ₗ Nᵢ) → (⨂ᵢ Mᵢ →ₗ ⨂ᵢ Nᵢ)`,  `⨂ᵢ fᵢ ↦ ⨂ᵢ mᵢ ↦ ⨂ᵢ fᵢ mᵢ`,

defined for arbitrary families of modules over a commutative semiring. This file proves that it is
**bijective** as soon as the index type is finite and every `Mᵢ` is finite projective, with the
`Nᵢ` arbitrary, and packages the result as the linear equivalence
`PiTensorProduct.piTensorHomEquiv`. This is the `ι`-ary form of Mathlib's
`TensorProduct.homTensorHomEquiv`, under the same hypotheses.

For finite free `Mᵢ` the proof is a basis computation: a basis `bᵢ` of `Mᵢ` indexed by a finite
`κᵢ` identifies `Mᵢ →ₗ Nᵢ` with the functions `κᵢ → Nᵢ`, the tensored basis identifies
`⨂ᵢ Mᵢ →ₗ ⨂ᵢ Nᵢ` with the functions `(∀ i, κᵢ) → ⨂ᵢ Nᵢ`, and under these identifications the
comparison map is the distributivity of the tensor product over finite direct sums,
`PiTensorProduct.ofDFinsuppEquiv`. A finite projective module is a retract of a finite free one,
and precomposition with the retraction data transports bijectivity. This step adapts the retract
argument in the proof of Mathlib's `dualTensorHom_bijective`
(`Mathlib/LinearAlgebra/Contraction.lean`).

Taking `Nᵢ = Mᵢ` this identifies `End (⨂ᵢ Mᵢ)` with `⨂ᵢ End Mᵢ`, compatibly with composition
(`PiTensorProduct.piTensorHomEquiv_tprod_comp_tprod`). That identification is the shape in which the
commutant computations of Schur-Weyl duality are run: the endomorphisms of a tensor power commuting
with the permutations of the factors are the invariants of the permutation action on the tensor
power of the endomorphism algebra.

## Main definitions

* `PiTensorProduct.piTensorHomEquiv`: the comparison map as a linear equivalence, for a finite
  index type and finite projective source modules.

## Main results

* `PiTensorProduct.piTensorHomMap_bijective_of_basis`: bijectivity of the comparison map from a
  family of finite bases of the source modules.
* `PiTensorProduct.piTensorHomMap_bijective`: bijectivity for finite projective source modules.
* `PiTensorProduct.piTensorHomEquiv_tprod_comp_tprod`: the equivalence turns the factorwise
  composition of two pure tensors of linear maps into the composition of their images.

## References

* W. Fulton and J. Harris, *Representation Theory: A First Course*, Appendix B.1.
-/

public section

open Module

open scoped TensorProduct

namespace PiTensorProduct

universe uι uR uM uN uP uκ

variable {ι : Type uι} {R : Type uR} {M : ι → Type uM} {N : ι → Type uN}
  [CommSemiring R] [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]
  [∀ i, AddCommMonoid (N i)] [∀ i, Module R (N i)]

section Bijective

variable [Finite ι]

/-- **The comparison map is bijective**, given a finite basis of every `Mᵢ`; the `Nᵢ` are
arbitrary. -/
theorem piTensorHomMap_bijective_of_basis {κ : ι → Type uκ} [∀ i, Finite (κ i)]
    (b : ∀ i, Basis (κ i) R (M i)) :
    Function.Bijective (piTensorHomMap (R := R) (s := M) (t := N)) := by
  classical
  have : Fintype ι := Fintype.ofFinite ι
  have : ∀ i, Fintype (κ i) := fun i => Fintype.ofFinite (κ i)
  -- `Mᵢ →ₗ Nᵢ ≃ (κᵢ → Nᵢ)` through `bᵢ`, distribute the tensor product over the finite direct
  -- sums, and `((∀ i, κᵢ) → ⨂ᵢ Nᵢ) ≃ (⨂ᵢ Mᵢ →ₗ ⨂ᵢ Nᵢ)` through the tensored basis.
  let e : (⨂[R] i, M i →ₗ[R] N i) ≃ₗ[R] ((⨂[R] i, M i) →ₗ[R] ⨂[R] i, N i) :=
    PiTensorProduct.congr (fun i => ((b i).constr R).symm ≪≫ₗ
      DFinsupp.linearEquivFunOnFintype.symm) ≪≫ₗ ofDFinsuppEquiv ≪≫ₗ
      DFinsupp.linearEquivFunOnFintype ≪≫ₗ (Basis.piTensorProduct b).constr R
  have he : piTensorHomMap (R := R) (s := M) (t := N) = e.toLinearMap :=
    PiTensorProduct.ext <| MultilinearMap.ext fun f =>
      (Basis.piTensorProduct b).ext fun p => by
        -- `Basis.constr_basis` has to fire before the tensored basis vector is unfolded.
        simp only [LinearMap.compMultilinearMap_apply, LinearEquiv.coe_coe, e,
          LinearEquiv.trans_apply, Basis.constr_basis]
        simp only [Basis.piTensorProduct_apply, piTensorHomMap_tprod_tprod, congr_tprod,
          LinearEquiv.trans_apply, DFinsupp.linearEquivFunOnFintype_apply,
          ofDFinsuppEquiv_tprod_apply]
        -- Evaluating a `DFinsupp` built from a function is evaluating the function.
        simp only [← DFinsupp.linearEquivFunOnFintype_apply (R := R), LinearEquiv.apply_symm_apply,
          Basis.constr_symm_apply]
  rw [he]
  exact e.bijective

variable [∀ i, Module.Projective R (M i)] [∀ i, Module.Finite R (M i)]

/-- **The comparison map `⨂ᵢ (Mᵢ →ₗ Nᵢ) → (⨂ᵢ Mᵢ →ₗ ⨂ᵢ Nᵢ)` is bijective** over a finite index
type when every `Mᵢ` is finite projective; the `Nᵢ` are arbitrary. -/
theorem piTensorHomMap_bijective :
    Function.Bijective (piTensorHomMap (R := R) (s := M) (t := N)) := by
  -- Each `Mᵢ` is a retract `fᵢ ∘ₗ gᵢ = id` of a finite free module `Fᵢ`, where the comparison map
  -- is bijective. Precomposition with the `fᵢ` and the `gᵢ` intertwines the two comparison maps.
  -- This adapts the retract argument of Mathlib's `dualTensorHom_bijective`
  -- (`Mathlib/LinearAlgebra/Contraction.lean`) to the `ι`-ary comparison map.
  choose n f g _ _ hfg using fun i => Module.Finite.exists_comp_eq_id_of_projective R (M i)
  have hF := piTensorHomMap_bijective_of_basis (N := N) fun i => Pi.basisFun R (Fin (n i))
  have hf : piTensorHomMap ∘ₗ (map fun i => (f i).lcomp R (N i)) =
      (map f).lcomp R _ ∘ₗ piTensorHomMap := by
    ext φ
    simp
  have hg : piTensorHomMap ∘ₗ (map fun i => (g i).lcomp R (N i)) =
      (map g).lcomp R _ ∘ₗ piTensorHomMap := by
    ext φ
    simp
  refine ⟨.of_comp (f := (map f).lcomp R _) ?_, .of_comp (g := map fun i => (g i).lcomp R (N i)) ?_⟩
  · rw [← LinearMap.coe_comp, ← hf, LinearMap.coe_comp]
    refine hF.1.comp (LinearMap.injective_of_comp_eq_id _ (map fun i => (g i).lcomp R (N i)) ?_)
    ext φ
    simp [LinearMap.lcomp_apply', LinearMap.comp_assoc, hfg]
  · rw [← LinearMap.coe_comp, hg, LinearMap.coe_comp]
    refine (LinearMap.surjective_of_comp_eq_id ((map f).lcomp R _) _ ?_).comp hF.2
    have hfg' (i) (x) : f i (g i x) = x := LinearMap.congr_fun (hfg i) x
    ext φ
    simp [hfg']

variable (R M N) in
/-- **The tensor product of the hom modules is the hom module of the tensor products.** The
underlying map is `PiTensorProduct.piTensorHomMap`, so this is a statement about a canonical map
and not about a choice of bases, even though the proof makes one. -/
noncomputable def piTensorHomEquiv :
    (⨂[R] i, M i →ₗ[R] N i) ≃ₗ[R] ((⨂[R] i, M i) →ₗ[R] ⨂[R] i, N i) :=
  LinearEquiv.ofBijective piTensorHomMap piTensorHomMap_bijective

/-- The equivalence acts as the comparison map it is built from. The priority is low so that the
more specific `PiTensorProduct.piTensorHomEquiv_tprod` still reaches its own normal form
`PiTensorProduct.map` on a pure tensor, which this rule would otherwise strand at
`PiTensorProduct.piTensorHomMap`. -/
@[simp low]
theorem piTensorHomEquiv_apply (x : ⨂[R] i, M i →ₗ[R] N i) :
    piTensorHomEquiv R M N x = piTensorHomMap x :=
  (rfl)

/-- The equivalence and the comparison map have the same underlying function. -/
theorem coe_piTensorHomEquiv :
    ⇑(piTensorHomEquiv R M N) = ⇑(piTensorHomMap (R := R) (s := M) (t := N)) :=
  (rfl)

/-- On a pure tensor of linear maps the equivalence is `PiTensorProduct.map`. -/
@[simp]
theorem piTensorHomEquiv_tprod (f : ∀ i, M i →ₗ[R] N i) :
    piTensorHomEquiv R M N (tprod R f) = map f := by
  rw [piTensorHomEquiv_apply, piTensorHomMap_tprod_eq_map]

/-- The inverse of the equivalence takes the factorwise map back to the pure tensor. -/
@[simp]
theorem piTensorHomEquiv_symm_map (f : ∀ i, M i →ₗ[R] N i) :
    (piTensorHomEquiv R M N).symm (map f) = tprod R f :=
  (LinearEquiv.symm_apply_eq _).mpr (piTensorHomEquiv_tprod f).symm

section Comp

variable {P : ι → Type uP} [∀ i, AddCommMonoid (P i)] [∀ i, Module R (P i)]
  [∀ i, Module.Projective R (N i)] [∀ i, Module.Finite R (N i)]

/-- **The equivalence is functorial on pure tensors**: composing factorwise and then comparing is
comparing and then composing. For `Nᵢ = Pᵢ = Mᵢ` this is multiplicativity on pure tensors of
endomorphisms, which is what makes the identification usable on the subalgebras of
`End (⨂ᵢ Mᵢ)` that Schur-Weyl duality is about. -/
theorem piTensorHomEquiv_tprod_comp_tprod (f : ∀ i, N i →ₗ[R] P i) (g : ∀ i, M i →ₗ[R] N i) :
    piTensorHomEquiv R M P (tprod R fun i => f i ∘ₗ g i) =
      piTensorHomEquiv R N P (tprod R f) ∘ₗ piTensorHomEquiv R M N (tprod R g) := by
  simp [map_comp]

end Comp

end Bijective

end PiTensorProduct
