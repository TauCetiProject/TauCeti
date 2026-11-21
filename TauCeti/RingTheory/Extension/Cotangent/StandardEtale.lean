/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Etale.StandardEtale
import TauCeti.RingTheory.Etale.StandardEtaleQuotient
import TauCeti.RingTheory.Extension.Cotangent.FlatLift
import TauCeti.RingTheory.Extension.Cotangent.Rank
import TauCeti.RingTheory.Extension.Cotangent.Smooth

/-!
# Conormal modules of presentations through a standard étale algebra

Let `P` present an `R`-algebra `A` as `R[X] ⧸ I`, and let `Q` present an `A`-algebra `B` as
`A[Y] ⧸ K`. The composite presentation `R[X, Y] → B` has conormal module `J / J²`, and
Jacobi–Zariski gives the exact sequence `B ⊗[A] I/I² → J/J² → K/K² → 0`
(`Algebra.Generators.Cotangent.exact`). When `B` is a standard étale `A`-algebra the first map is
injective (`Algebra.Generators.liftBaseChange_injective_of_isStandardEtale`).
Since `B` is formally smooth over `A`, the conormal module `K/K²` is projective, so the sequence
splits: `J/J² ≃ B ⊗[A] I/I² × K/K²`
(`Algebra.Generators.cotangentCompEquivOfIsStandardEtale`). In particular, when `Q` is a
submersive presentation with finitely many relations and the fibre `F ⊗[A] I/I²` is
finite-dimensional, the fibres of the conormal modules at that field-valued point of `B` satisfy
`dim F ⊗[B] J/J² = dim F ⊗[A] I/I² + #relations of Q`
(`Algebra.Generators.finrank_tensor_cotangent_comp_of_isStandardEtale`). When the presentation
kernel `I` is finitely generated near the image point, Nakayama's lemma interprets these fibre
dimensions as the minimal numbers of generators of the localized presentation kernels.
This equation count is used to detect complete intersections on étale neighbourhoods.

Injectivity is the base change of a flatness statement. It holds whenever `B` lifts to a flat
`R[X]`-algebra `C` with `C ⧸ I C ≅ B`
(`Algebra.Generators.liftBaseChange_injective_of_flat_lift`, in
`TauCeti.RingTheory.Extension.Cotangent.FlatLift`), and standard étale algebras lift in this way
(`Algebra.IsStandardEtale.exists_flat_lift`).

The splitting and its simp lemmas follow Mathlib's
`Algebra.Generators.cotangentCompLocalizationAwayEquiv`
(`Mathlib/RingTheory/Extension/Cotangent/LocalizationAway.lean`), which splits the same
Jacobi–Zariski sequence when `B` is a localization of `A` away from one element.

## References

* [Stacks Project, Tag 00S2](https://stacks.math.columbia.edu/tag/00S2): the Jacobi–Zariski
  sequence of naive cotangent complexes.
* [Stacks Project, Section 10.135, Tag 00S8](https://stacks.math.columbia.edu/tag/00S8): local
  complete intersections.
-/

public section

open TensorProduct MvPolynomial

namespace Algebra.Generators

universe u v

variable {R : Type u} {A B : Type*} [CommRing R] [CommRing A] [CommRing B] [Algebra R A]
  [Algebra R B] [Algebra A B] [IsScalarTower R A B] {ι : Type v} {ι' : Type*}
  (Q : Generators A B ι') (P : Generators R A ι)

/-- For a standard étale `A`-algebra `B`, the map `B ⊗[A] I/I² → J/J²` from the conormal module of
a presentation of `A` to that of the composite presentation `R[X, Y] → B` is injective. -/
theorem liftBaseChange_injective_of_isStandardEtale
    [Algebra.IsStandardEtale A B] :
    Function.Injective
      ((Extension.Cotangent.map (Q.toComp P).toExtensionHom).liftBaseChange B) := by
  obtain ⟨C, _, _, _, φ, hφ, hφalg, hker⟩ :=
    Algebra.IsStandardEtale.exists_flat_lift (S := P.Ring) (B := B) P.algebraMap_surjective
  exact liftBaseChange_injective_of_flat_lift Q P φ hφ hφalg hker

variable [Algebra.IsStandardEtale A B]

/-- (Implementation) The splitting of the Jacobi–Zariski sequence of `R[X, Y] → B`, bundled with
its compatibility with the maps of the sequence. Since `B` is formally smooth over `A`, the
conormal module `K/K²` is projective (`Algebra.Extension.projective_cotangent_of_formallySmooth`),
so the projection `J/J² → K/K²` has a section. -/
private noncomputable def cotangentCompSplitting :=
  haveI : Algebra.FormallySmooth A Q.toExtension.Ring := instFormallySmoothMvPolynomial ι'
  haveI := Q.toExtension.projective_cotangent_of_formallySmooth
  (Cotangent.exact Q P).splitSurjectiveEquiv (liftBaseChange_injective_of_isStandardEtale Q P)
    ⟨_, (Module.projective_lifting_property _ LinearMap.id
      (Cotangent.surjective_map_ofComp Q P)).choose_spec⟩

/-- For a standard étale `A`-algebra `B` presented by `Q`, the conormal module `J/J²` of the
composite presentation `R[X, Y] → B` splits as `B ⊗[A] I/I² × K/K²`. -/
noncomputable def cotangentCompEquivOfIsStandardEtale :
    (Q.comp P).toExtension.Cotangent ≃ₗ[B]
      B ⊗[A] P.toExtension.Cotangent × Q.toExtension.Cotangent :=
  (cotangentCompSplitting Q P).val

/-- The splitting restricts to `B ⊗[A] I/I² → J/J²` on the first factor. -/
theorem cotangentCompEquivOfIsStandardEtale_symm_comp_inl :
    (cotangentCompEquivOfIsStandardEtale Q P).symm.toLinearMap ∘ₗ LinearMap.inl B _ _ =
      (Extension.Cotangent.map (Q.toComp P).toExtensionHom).liftBaseChange B :=
  (cotangentCompSplitting Q P).property.1.symm

/-- The second component of the splitting is the projection `J/J² → K/K²`. -/
theorem snd_comp_cotangentCompEquivOfIsStandardEtale :
    LinearMap.snd B _ _ ∘ₗ (cotangentCompEquivOfIsStandardEtale Q P).toLinearMap =
      Extension.Cotangent.map (Q.ofComp P).toExtensionHom :=
  (cotangentCompSplitting Q P).property.2.symm

/-- Pointwise form of `cotangentCompEquivOfIsStandardEtale_symm_comp_inl`. -/
@[simp]
lemma cotangentCompEquivOfIsStandardEtale_symm_inl (a : B ⊗[A] P.toExtension.Cotangent) :
    (cotangentCompEquivOfIsStandardEtale Q P).symm (a, 0) =
      LinearMap.liftBaseChange B (Extension.Cotangent.map (Q.toComp P).toExtensionHom) a :=
  LinearMap.congr_fun (cotangentCompEquivOfIsStandardEtale_symm_comp_inl Q P) a

/-- The splitting sends the image of `B ⊗[A] I/I²` to the first factor. -/
@[simp]
lemma cotangentCompEquivOfIsStandardEtale_liftBaseChange (a : B ⊗[A] P.toExtension.Cotangent) :
    cotangentCompEquivOfIsStandardEtale Q P
        (LinearMap.liftBaseChange B (Extension.Cotangent.map (Q.toComp P).toExtensionHom) a) =
      (a, 0) := by
  rw [← cotangentCompEquivOfIsStandardEtale_symm_inl, LinearEquiv.apply_symm_apply]

/-- Pointwise form of `snd_comp_cotangentCompEquivOfIsStandardEtale`. -/
@[simp]
lemma snd_cotangentCompEquivOfIsStandardEtale (a : (Q.comp P).toExtension.Cotangent) :
    (cotangentCompEquivOfIsStandardEtale Q P a).2 =
      Extension.Cotangent.map (Q.ofComp P).toExtensionHom a :=
  LinearMap.congr_fun (snd_comp_cotangentCompEquivOfIsStandardEtale Q P) a

/-- Through a standard étale `A`-algebra `B` with a submersive presentation `Q` with finitely many
relations, the fibre at a field-valued point `F` of `B` of the conormal module of the composite
presentation `R[X, Y] → B` has dimension the dimension of the fibre of the conormal module of `P`,
plus the number of relations of `Q`, provided the fibre `F ⊗[A] I/I²` of the conormal module of
`P` is finite-dimensional. -/
theorem finrank_tensor_cotangent_comp_of_isStandardEtale {σ : Type*} [Finite σ]
    (Q : SubmersivePresentation A B ι' σ) (F : Type*) [Field F] [Algebra A F] [Algebra B F]
    [IsScalarTower A B F] [Module.Finite F (F ⊗[A] P.toExtension.Cotangent)] :
    Module.finrank F (F ⊗[B] (Q.toGenerators.comp P).toExtension.Cotangent) =
      Module.finrank F (F ⊗[A] P.toExtension.Cotangent) + Nat.card σ := by
  have : Nontrivial B := (algebraMap B F).domain_nontrivial
  have := Fintype.ofFinite σ
  have : Module.Finite B Q.toExtension.Cotangent := .of_basis Q.basisCotangent
  -- The splitting, transported to the fibre; the conormal module of `Q` is free on its relations.
  rw [finrank_tensor_cotangent_comp_of_linearEquiv _ P
      (cotangentCompEquivOfIsStandardEtale Q.toGenerators P),
    (Q.cotangentEquiv.baseChange B F _ _).finrank_eq,
    Module.finrank_baseChange (R := F) (M' := σ → B), Module.finrank_fintype_fun_eq_card,
    Nat.card_eq_fintype_card]

end Algebra.Generators
