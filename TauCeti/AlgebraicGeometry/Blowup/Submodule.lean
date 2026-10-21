/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
public import TauCeti.RingTheory.GradedAlgebra.CoeffSubalgebra

/-!
# The blowup of a submodule

Let `B` be a `C`-algebra, `F ⊆ B` a set and `J = span C F` the `C`-submodule of `B` it spans. The
graded ring `R(J) = ⨁ₙ Jⁿ Tⁿ ⊆ B[T]`, with `J⁰` the image of `C`, is `TauCeti.coeffSubalgebra` of
the powers `n ↦ Jⁿ`, and it is generated over `C` by the elements `f T` with `f ∈ F`. Its `Proj`

`Y = Proj R(J) ⟶ Spec C`

is the *blowup of the submodule `J`*. When `B = C` and `J` is an ideal, `R(J)` is the Rees
algebra (`reesAlgebra_eq_coeffSubalgebra`) and `Y` is the blowup of `Spec C` along `V(J)`. For a
general ring map `C → B`, this is the scheme used in Huber's proof that a complete Huber ring `B`
with a noetherian ring of definition `C` is sheafy, applied to generators `F` of the unit ideal of
`B` that define a standard rational covering of `Spa B`.

The construction of `Y` needs no hypothesis on `F`, and the standard opens `D₊(f T)`, `f ∈ F`,
cover it. If `F` is finite, `Y` is proper over `Spec C`, and noetherian when `C` is. If `F`
generates the unit ideal of `B`, then the image of the irrelevant ideal of `R(J)` under
evaluation at `T = 1` generates the unit ideal of `B`, and so evaluation defines a morphism
`Spec B ⟶ Y` over `Spec C`; the standard open `D₊(f T)` pulls back to the basic open `D(f)`, and
this morphism is affine.

## Main definitions

* `TauCeti.AlgebraicGeometry.submoduleBlowup.gradedRing C F`: the graded ring `R(J)`.
* `TauCeti.AlgebraicGeometry.submoduleBlowup C F`: the scheme `Proj R(J)`.
* `TauCeti.AlgebraicGeometry.submoduleBlowup.monomialDegreeOne C hf`: the element `f T` of
  `R(J)`, for `f ∈ F`.
* `TauCeti.AlgebraicGeometry.submoduleBlowup.toSpec C F`: the structure morphism to `Spec C`.
* `TauCeti.AlgebraicGeometry.submoduleBlowup.fromSpec C hF`: the morphism `Spec B ⟶ Y`, when
  `F` generates the unit ideal of `B`.

## Main results

* `TauCeti.AlgebraicGeometry.submoduleBlowup.iSup_basicOpen_eq_top`: the standard opens
  `D₊(f T)`, `f ∈ F`, cover `Y`.
* `TauCeti.AlgebraicGeometry.submoduleBlowup.isProper_toSpec`: for finite `F`, `Y ⟶ Spec C` is
  proper.
* `TauCeti.AlgebraicGeometry.submoduleBlowup.isNoetherian`: for finite `F` and noetherian `C`, `Y`
  is noetherian.
* `TauCeti.AlgebraicGeometry.submoduleBlowup.fromSpec_toSpec`: `Spec B ⟶ Y` is a morphism over
  `Spec C`.
* `TauCeti.AlgebraicGeometry.submoduleBlowup.fromSpec_preimage_basicOpen`: `D₊(f T)` pulls back
  to `D(f)`.
* `TauCeti.AlgebraicGeometry.submoduleBlowup.isAffineHom_fromSpec`: `Spec B ⟶ Y` is affine.

## References

* R. Huber, *A generalization of formal schemes and rigid analytic varieties*, Math. Z. 217
  (1994), §2, proof of Theorem 2.5, Case I, (1.1) and (1.2)(i).
* [The Stacks Project, Section *Blowing up*](https://stacks.math.columbia.edu/tag/01OF)
-/

public section

open CategoryTheory

universe u

namespace TauCeti.AlgebraicGeometry

open _root_.AlgebraicGeometry

namespace submoduleBlowup

section GradedRing

variable (C : Type*) {B : Type*} [CommRing C] [CommRing B] [Algebra C B] (F : Set B)

/-- The graded ring `R(J) = ⨁ₙ Jⁿ Tⁿ ⊆ B[T]` of the submodule `J = span C F` of the `C`-algebra
`B`, graded by the power of `T`. Its degree `n` piece consists of the monomials `b Tⁿ` with
`b ∈ Jⁿ`. -/
noncomputable abbrev gradedRing :
    ℕ → Submodule C (coeffSubalgebra fun n ↦ Submodule.span C F ^ n) :=
  coeffSubalgebra.grade fun n ↦ Submodule.span C F ^ n

variable {F} in
/-- The element `f T` of degree one of `R(J)`, for `f ∈ F`. -/
noncomputable def monomialDegreeOne {f : B} (hf : f ∈ F) :
    coeffSubalgebra fun n ↦ Submodule.span C F ^ n :=
  coeffSubalgebra.monomial _ 1 f (by rw [pow_one]; exact Submodule.subset_span hf)

variable {F} in
@[simp]
theorem coe_monomialDegreeOne {f : B} (hf : f ∈ F) :
    (monomialDegreeOne C hf : Polynomial B) = Polynomial.monomial 1 f :=
  coeffSubalgebra.coe_monomial _ _ _

variable {F} in
theorem monomialDegreeOne_mem_gradedRing {f : B} (hf : f ∈ F) :
    monomialDegreeOne C hf ∈ gradedRing C F 1 :=
  coeffSubalgebra.monomial_mem_grade 1 f _

/-- `R(J)` is generated over its degree zero part by the elements `f T` with `f ∈ F`. -/
theorem adjoin_monomialDegreeOne_eq_top :
    Algebra.adjoin (gradedRing C F 0) (Set.range fun f : F ↦ monomialDegreeOne C f.2) = ⊤ := by
  -- The degree zero part acts through multiplication in `R(J)`, compatibly with `C`.
  have : IsScalarTower C (gradedRing C F 0) (coeffSubalgebra fun n ↦ Submodule.span C F ^ n) :=
    ⟨fun c a x ↦ smul_mul_assoc c (a : coeffSubalgebra fun n ↦ Submodule.span C F ^ n) x⟩
  have h : Algebra.adjoin C (Set.range fun f : F ↦ monomialDegreeOne C f.2) = ⊤ :=
    coeffSubalgebra.adjoin_monomial_one_eq_top F
  refine eq_top_iff.mpr fun x _ ↦ ?_
  have hx : x ∈ Algebra.adjoin C (Set.range fun f : F ↦ monomialDegreeOne C f.2) := by
    rw [h]
    exact Algebra.mem_top
  exact Algebra.adjoin_le (S := (Algebra.adjoin (gradedRing C F 0)
    (Set.range fun f : F ↦ monomialDegreeOne C f.2)).restrictScalars C) Algebra.subset_adjoin hx

variable {F} in
/-- Evaluation of `R(J) ⊆ B[T]` at `T = 1` sends `f T` to `f`. -/
@[simp]
theorem evalOne_monomialDegreeOne {f : B} (hf : f ∈ F) :
    coeffSubalgebra.evalOne _ (monomialDegreeOne C hf) = f :=
  coeffSubalgebra.evalOne_monomial _ _ _

variable {F} in
/-- If `F` generates the unit ideal of `B`, the ideal of `B` generated by the image of the
irrelevant ideal of `R(J)` under evaluation at `T = 1` is all of `B`. -/
theorem map_evalOne_irrelevant (hF : Ideal.span F = ⊤) :
    (HomogeneousIdeal.irrelevant (gradedRing C F)).toIdeal.map (coeffSubalgebra.evalOne _) = ⊤ := by
  rw [eq_top_iff, ← hF, Ideal.span_le]
  intro f hf
  rw [SetLike.mem_coe, ← evalOne_monomialDegreeOne C hf]
  exact Ideal.mem_map_of_mem _ (HomogeneousIdeal.mem_irrelevant_of_mem _ one_pos
    (monomialDegreeOne_mem_gradedRing C hf))

end GradedRing

end submoduleBlowup

variable (C : Type u) {B : Type u} [CommRing C] [CommRing B] [Algebra C B] (F : Set B)

/-- **The blowup of a submodule.** The scheme `Proj R(J)` of the graded ring
`R(J) = ⨁ₙ Jⁿ Tⁿ` of the submodule `J = span C F` of the `C`-algebra `B`. -/
noncomputable abbrev submoduleBlowup : Scheme.{u} :=
  Proj (submoduleBlowup.gradedRing C F)

namespace submoduleBlowup

/-- The structure morphism `Proj R(J) ⟶ Spec C`: the projection to the spectrum of the degree
zero part of `R(J)`, followed by the spectrum of the structure map of `C`. -/
noncomputable def toSpec : submoduleBlowup C F ⟶ Spec (.of C) :=
  Proj.toSpecZero (gradedRing C F) ≫
    Spec.map (CommRingCat.ofHom (algebraMap C (gradedRing C F 0)))

/-- The structure morphism is `Proj.toSpecZero` followed by `Spec R(J)₀ ⟶ Spec C`. -/
theorem toSpec_def : toSpec C F = Proj.toSpecZero (gradedRing C F) ≫
    Spec.map (CommRingCat.ofHom (algebraMap C (gradedRing C F 0))) :=
  (rfl)

/-- **The standard opens `D₊(f T)` cover the blowup.** -/
theorem iSup_basicOpen_eq_top :
    ⨆ f : F, Proj.basicOpen (gradedRing C F) (monomialDegreeOne C f.2) = ⊤ :=
  Proj.iSup_basicOpen_eq_top' (gradedRing C F) (fun f : F ↦ monomialDegreeOne C f.2)
    (fun f ↦ ⟨1, monomialDegreeOne_mem_gradedRing C f.2⟩) (adjoin_monomialDegreeOne_eq_top C F)

/-- The second factor `Spec R(J)₀ ⟶ Spec C` of the structure morphism is a closed immersion. -/
instance : IsClosedImmersion (Spec.map (R := .of C) (S := .of (gradedRing C F 0))
    (CommRingCat.ofHom (algebraMap C (gradedRing C F 0)))) :=
  IsClosedImmersion.spec_of_surjective _
    (coeffSubalgebra.algebraMap_grade_pow_zero_surjective (Submodule.span C F))

variable {F}

/-- **The blowup of a finitely generated submodule is proper.** If `F` is finite, the structure
morphism `Proj R(J) ⟶ Spec C` is proper. -/
theorem isProper_toSpec (hF : F.Finite) : IsProper (toSpec C F) := by
  have : Algebra.FiniteType (gradedRing C F 0) (coeffSubalgebra fun n ↦ Submodule.span C F ^ n) :=
    ⟨Subalgebra.fg_def.mpr ⟨_, @Set.finite_range _ _ _ hF.to_subtype,
      adjoin_monomialDegreeOne_eq_top C F⟩⟩
  rw [toSpec]
  infer_instance

/-- If `C` is noetherian and `F` is finite, the blowup `Proj R(J)` is a noetherian scheme. -/
theorem isNoetherian (hF : F.Finite) [IsNoetherianRing C] :
    _root_.AlgebraicGeometry.IsNoetherian (submoduleBlowup C F) :=
  have := isProper_toSpec C hF
  { toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian (toSpec C F)
    toCompactSpace := QuasiCompact.compactSpace_of_compactSpace (toSpec C F) }

/-- The morphism `Spec B ⟶ Proj R(J)` defined by evaluation at `T = 1`, when `F` generates the
unit ideal of `B`. -/
noncomputable def fromSpec (hF : Ideal.span F = ⊤) : Spec (.of B) ⟶ submoduleBlowup C F :=
  Proj.fromOfGlobalSections (gradedRing C F)
    ((Scheme.ΓSpecIso (.of B)).inv.hom.comp (coeffSubalgebra.evalOne _).toRingHom) <| by
      -- Evaluation maps the irrelevant ideal onto the unit ideal, and so does `ΓSpecIso`.
      rw [← Ideal.map_map, ← Ideal.map_top (Scheme.ΓSpecIso (.of B)).inv.hom]
      exact congrArg _ (map_evalOne_irrelevant C hF)

/-- `Spec B ⟶ Proj R(J)` is the morphism to `Proj` defined by evaluation at `T = 1`, as a map to
the global sections of `Spec B`. -/
theorem fromSpec_def (hF : Ideal.span F = ⊤) :
    ∀ h, fromSpec C hF = Proj.fromOfGlobalSections (gradedRing C F)
      ((Scheme.ΓSpecIso (.of B)).inv.hom.comp (coeffSubalgebra.evalOne _).toRingHom) h :=
  fun _ ↦ (rfl)

/-- The morphism `Spec B ⟶ Proj R(J)` is a morphism over `Spec C`: followed by the structure
morphism of the blowup, it is the spectrum of the structure map `C → B`. -/
@[reassoc (attr := simp)]
theorem fromSpec_toSpec (hF : Ideal.span F = ⊤) :
    fromSpec C hF ≫ toSpec C F = Spec.map (CommRingCat.ofHom (algebraMap C B)) := by
  -- Insert `toSpecΓ ≫ Spec.map (ΓSpecIso B).inv = 𝟙` on the right, so that both sides are
  -- `toSpecΓ` followed by `Spec` of a ring map `C → Γ(Spec B, ⊤)`. Both ring maps are `C → B`
  -- followed by `ΓSpecIso.inv`, since evaluation at `T = 1` is a `C`-algebra map.
  rw [fromSpec, toSpec, Proj.fromOfGlobalSections_toSpecZero_assoc, ← Spec.map_comp,
    ← toSpecΓ_SpecMap_ΓSpecIso_inv_assoc _ (Spec.map (CommRingCat.ofHom (algebraMap C B))),
    ← Spec.map_comp]
  congr 2
  ext c
  exact congrArg (Scheme.ΓSpecIso (.of B)).inv.hom ((coeffSubalgebra.evalOne _).commutes c)

/-- The standard open `D₊(f T)` of `Proj R(J)` pulls back to the basic open `D(f)` of `Spec B`. -/
@[simp]
theorem fromSpec_preimage_basicOpen (hF : Ideal.span F = ⊤) {f : B} (hf : f ∈ F) :
    fromSpec C hF ⁻¹ᵁ Proj.basicOpen (gradedRing C F) (monomialDegreeOne C hf) =
      PrimeSpectrum.basicOpen f := by
  rw [fromSpec, Proj.fromOfGlobalSections_preimage_basicOpen _ _ _ one_pos
    (monomialDegreeOne_mem_gradedRing C hf)]
  -- The section cutting out the preimage is `ΓSpecIso.inv f`, as evaluation sends `f T` to `f`.
  convert basicOpen_eq_of_affine (R := .of B) f using 2
  simp

/-- The morphism `Spec B ⟶ Proj R(J)` is affine: the standard opens `D₊(f T)` are affine, and so
are their preimages `D(f)`. -/
instance isAffineHom_fromSpec (hF : Ideal.span F = ⊤) : IsAffineHom (fromSpec C hF) := by
  refine isAffineHom_of_forall_exists_isAffineOpen _ fun y ↦ ?_
  obtain ⟨⟨f, hf⟩, hy⟩ := TopologicalSpace.Opens.mem_iSup.mp
    ((iSup_basicOpen_eq_top C F).ge (Set.mem_univ y))
  refine ⟨_, hy, Proj.isAffineOpen_basicOpen _ _ (monomialDegreeOne_mem_gradedRing C hf) one_pos,
    ?_⟩
  rw [fromSpec_preimage_basicOpen]
  exact IsAffineOpen.Spec_basicOpen (R := .of B) f

end submoduleBlowup

end TauCeti.AlgebraicGeometry
