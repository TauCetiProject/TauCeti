/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Flat.Equalizer
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import TauCeti.RingTheory.Flat.TensorProduct
import TauCeti.LinearAlgebra.TensorProduct.ScalarExtension

/-!
# The fibrewise criterion for flatness of finitely presented modules

Let `R → B` be a ring homomorphism and `M` a finitely presented `B`-module which is flat over
`R`. If for every prime `p` of `R` the base change of `M` to the fibre ring `B ⊗[R] κ(p)` is flat
over `B ⊗[R] κ(p)`, then `M` is flat over `B` (`Module.Flat.of_flat_fiber`). Geometrically: a
finite and finitely presented morphism `X ⟶ Y` of schemes over `S`, with `X` flat over `S`, is
flat as soon as its restriction to every fibre over `S` is flat. This deduces flatness of a finite
morphism between two families over `S` from flatness over fields, as is needed for
multiplication by an integer on an elliptic curve over an arbitrary base.

The local statement is `Module.Free.of_flat_fiber`: if `B` is local and `p` is the inverse image
of its maximal ideal in `R`, flatness of `M` over `R` and of its fibre `(B ⊗[R] κ(p)) ⊗[B] M` over
`B ⊗[R] κ(p)` make `M` free over `B`. Choose a presentation `0 → K → Bⁿ → M → 0`. As `M` is flat
over `R`, the sequence stays exact after `κ(p) ⊗[R] -`, which is base change along
`B → B ⊗[R] κ(p)`; as the fibre of `M` is flat, it stays exact after a further base change to
the residue field of `B`. So `κ(B) ⊗[B] K → κ(B)ⁿ` is injective, and Mathlib's
`Module.free_of_lTensor_residueField_injective` shows that `M` is free. No Noetherian hypothesis
is needed: finite presentation makes `K` finitely generated, which is what Nakayama's lemma
uses.

The global statement localizes at the maximal ideals `q` of `B`. The localization `B_q ⊗[B] M`
is still flat over `R` (`Module.Flat.tensorProduct_of_flat`), and its fibre over the prime of `R`
below `q` is a base change of the fibre of `M`.

## Main results

* `Module.Free.of_flat_fiber`: the criterion over a local ring, with freeness as conclusion.
* `Module.Flat.of_flat_fiber`: the criterion over an arbitrary ring.

## References

* A. Grothendieck, *Éléments de géométrie algébrique IV*, troisième partie, Théorème 11.3.10,
  the *critère de platitude par fibres*.
* The Stacks Project, Lemma 10.99.15 (Tag 00MP), the Noetherian version.
-/

public section

open TensorProduct IsLocalRing

namespace Module

variable {R B M : Type*} [CommRing R] [CommRing B] [Algebra R B]
  [AddCommGroup M] [Module R M] [Module B M] [IsScalarTower R B M]

/-- **The fibrewise criterion for flatness, local form.** Let `B` be a local `R`-algebra and `p`
the inverse image in `R` of the maximal ideal of `B`. A finitely presented `B`-module `M` which
is flat over `R`, and whose fibre `(B ⊗[R] κ(p)) ⊗[B] M` is flat over `B ⊗[R] κ(p)`, is free
over `B`. -/
theorem Free.of_flat_fiber [IsLocalRing B] [Module.FinitePresentation B M] [Flat R M]
    (h : Flat (B ⊗[R] ((maximalIdeal B).comap (algebraMap R B)).ResidueField)
      ((B ⊗[R] ((maximalIdeal B).comap (algebraMap R B)).ResidueField) ⊗[B] M)) :
    Free B M := by
  set p := (maximalIdeal B).comap (algebraMap R B)
  set k := p.ResidueField
  set F := B ⊗[R] k
  -- The residue field of `B` is an algebra over the fibre ring `F`.
  let φ : k →ₐ[R] ResidueField B :=
    Ideal.ResidueField.liftₐ p (Algebra.ofId R (ResidueField B))
      (fun r hr ↦ by
        simpa [IsScalarTower.algebraMap_apply R B (ResidueField B), p] using hr)
      (fun r hr ↦ by
        simpa [IsScalarTower.algebraMap_apply R B (ResidueField B), IsUnit.mem_submonoid_iff,
          residue_ne_zero_iff_isUnit, p] using hr)
  let ψ : F →ₐ[B] ResidueField B :=
    Algebra.TensorProduct.lift (Algebra.ofId B _) φ fun _ _ ↦ .all _ _
  let : Algebra F (ResidueField B) := ψ.toAlgebra
  have : IsScalarTower B F (ResidueField B) :=
    .of_algebraMap_eq fun b ↦ (ψ.commutes b).symm
  -- A presentation `0 → K → Bⁿ → M → 0`, with `K` finitely generated.
  obtain ⟨n, g, hg⟩ := Module.Finite.exists_fin' B M
  have : Module.Finite B (LinearMap.ker g) := .of_fg (Module.FinitePresentation.fg_ker g hg)
  have hex := LinearMap.exact_subtype_ker_map g
  refine free_of_lTensor_residueField_injective _ g hg hex ?_
  -- `F ⊗[B] K → F ⊗[B] Bⁿ` is injective, since `M` is flat over `R`.
  have h₁ : Function.Injective ((LinearMap.ker g).subtype.baseChange F) := by
    rw [LinearMap.baseChange_eq_ltensor]
    exact (LinearMap.injective_lTensor_iff_injective_lTensor_restrictScalars k _).mpr <|
      LinearMap.lTensor_injective_of_exact_of_flat (g.restrictScalars R) hg _
        Subtype.val_injective hex k
  -- The fibre `F ⊗[B] M` is flat over `F`, so `κ(B) ⊗[F] (F ⊗[B] K) → κ(B) ⊗[F] (F ⊗[B] Bⁿ)` is
  -- injective too.
  have h₂ := LinearMap.lTensor_injective_of_exact_of_flat (g.baseChange F)
    (LinearMap.lTensor_surjective F hg) _ h₁ (lTensor_exact F hex hg) (ResidueField B)
  -- Through `κ(B) ⊗[F] (F ⊗[B] N) ≃ κ(B) ⊗[B] N`, this is `κ(B) ⊗[B] K → κ(B) ⊗[B] Bⁿ`.
  let e (N : Type _) [AddCommGroup N] [Module B N] :=
    AlgebraTensorModule.cancelBaseChange B F (ResidueField B) (ResidueField B) N
  have key := LinearMap.congr_fun (AlgebraTensorModule.lTensor_comp_cancelBaseChange B F
    (ResidueField B) (M := ResidueField B) (LinearMap.ker g).subtype)
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    AlgebraTensorModule.coe_lTensor] at key
  intro x y hxy
  obtain ⟨x, rfl⟩ := (e _).surjective x
  obtain ⟨y, rfl⟩ := (e _).surjective y
  rw [key, key] at hxy
  rw [h₂ ((e _).injective hxy)]

/-- **The fibrewise criterion for flatness.** Let `M` be a finitely presented `B`-module which is
flat over `R`. If for every prime `p` of `R` the fibre `(B ⊗[R] κ(p)) ⊗[B] M` is flat over the
fibre ring `B ⊗[R] κ(p)`, then `M` is flat over `B`. -/
theorem Flat.of_flat_fiber [Module.FinitePresentation B M] [Flat R M]
    (h : ∀ (p : Ideal R) [p.IsPrime],
      Flat (B ⊗[R] p.ResidueField) ((B ⊗[R] p.ResidueField) ⊗[B] M)) :
    Flat B M := by
  have (q : Ideal B) [q.IsMaximal] :
      IsLocalizedModule.AtPrime q (TensorProduct.mk B (Localization.AtPrime q) M 1) :=
    (isLocalizedModule_iff_isBaseChange q.primeCompl _ _).mpr (TensorProduct.isBaseChange B M _)
  refine flat_of_isLocalized_maximal (R := B) B M (fun q _ ↦ Localization.AtPrime q ⊗[B] M)
    (fun q _ ↦ TensorProduct.mk B (Localization.AtPrime q) M 1) fun q _ ↦ ?_
  set Bq := Localization.AtPrime q
  have : Flat R (Bq ⊗[B] M) := Flat.tensorProduct_of_flat Bq
  -- The fibre of `Bq ⊗[B] M` is the base change of the fibre of `M` along `F → F'`.
  set p := (maximalIdeal Bq).comap (algebraMap R Bq)
  let F := B ⊗[R] p.ResidueField
  let F' := Bq ⊗[R] p.ResidueField
  let ψ : F →ₐ[B] F' := Algebra.TensorProduct.map (IsScalarTower.toAlgHom B B Bq) (AlgHom.id R _)
  let : Algebra F F' := ψ.toAlgebra
  have : IsScalarTower B F F' := .of_algebraMap_eq fun b ↦ (ψ.commutes b).symm
  have := h p
  have : Free Bq (Bq ⊗[B] M) := Free.of_flat_fiber (R := R) <| Flat.of_linearEquiv
    ((AlgebraTensorModule.cancelBaseChange B Bq F' F' M).trans
      (AlgebraTensorModule.cancelBaseChange B F F' F' M).symm)
  exact Flat.trans B Bq _

end Module
