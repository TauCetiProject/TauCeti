/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

/-!
# The rigidity lemma

Let `X`, `Y`, `Z` be schemes over a field `K`, with `X` proper and geometrically integral, `Y`
geometrically integral and locally of finite type, and `Z` separated and locally of finite type.
The **rigidity lemma** says that a morphism `f : X ×_K Y ⟶ Z` which collapses one fibre
`X × {y₀}` over a `K`-rational point `y₀` of `Y` to a single `K`-rational point of `Z` factors
through the projection to `Y`: for any `K`-rational point `x₀` of `X`,
`f (x, y) = f (x₀, y)`.

Over an algebraically closed field the proof runs as follows. The morphism
`γ = (pr₂, f) : X × Y ⟶ Y × Z` is proper over `Y`, and its fibre over `y₀` has a single point
in its image. By Zariski's main theorem, `γ` has finite image on each fibre `X × {y}` for `y` in
an open neighbourhood `U` of `y₀`. For a closed point `y ∈ U`, the fibre `X × {y}` is
irreducible, so its finite image under `γ` is a single point; hence `f (x, y) = f (x₀, y)` on the
closed points of the dense open subset
`pr₂⁻¹ U`, and so everywhere, since `X × Y` is reduced and `Z` is separated. The general case
follows by base change to an algebraic closure, which is faithful on schemes over `Spec K`.

This is the argument of Mathlib's
`AlgebraicGeometry.isCommMonObj_of_isProper_of_isIntegral_tensorObj_of_isAlgClosed` (Andrew Yang
and Christian Merten), which proves commutativity of proper group schemes by running it for the
commutator map; here it is carried out for an arbitrary morphism `f`. The descent to an arbitrary
field follows `AlgebraicGeometry.isCommMonObj_of_isProper_of_geometricallyIntegral` in the same
Mathlib file (Andrew Yang and Christian Merten).

## Main declarations

* `TauCeti.AlgebraicGeometry.preimage_snd_left_eq_range_whiskerLeft_left`: the fibre of
  `X × Y ⟶ Y` over a `K`-rational point `y` is the image of `X × Y ⟶ X × Y`, `(x, y') ↦ (x, y)`;
* `TauCeti.AlgebraicGeometry.exists_forall_finite_image_preimage_of_finite_image_preimage`: if
  a morphism proper over a base has finite image on one fibre, it does so on the fibres over a
  neighbourhood;
* `TauCeti.AlgebraicGeometry.eq_snd_comp_lift_comp_of_isAlgClosed`: the rigidity lemma over an
  algebraically closed field;
* `TauCeti.AlgebraicGeometry.eq_snd_comp_lift_comp`: the rigidity lemma over an arbitrary field.

## References

* D. Mumford, *Abelian Varieties*, Section 4, the rigidity lemma.
* J. S. Milne, *Abelian Varieties*, Theorem 1.1.
-/

public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory

namespace TauCeti

namespace AlgebraicGeometry

open _root_.AlgebraicGeometry

universe u

variable {K : Type u} [Field K]

/-- The fibre of the second projection `X × Y ⟶ Y` over a `K`-rational point `y` of `Y` is the
range of the map `X × Y ⟶ X × Y`, `(x, y') ↦ (x, y)`. -/
lemma preimage_snd_left_eq_range_whiskerLeft_left (X Y : Over (Spec (.of K)))
    (y : 𝟙_ (Over (Spec (.of K))) ⟶ Y) :
    (snd X Y).left ⁻¹' {y.left (IsLocalRing.closedPoint K)} =
      Set.range (X ◁ (toUnit Y ≫ y)).left := by
  rw [Over.whiskerLeft_left, Scheme.Pullback.range_map]
  ext z
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_inter_iff, Set.mem_range]
  refine ⟨fun h ↦ ⟨⟨_, rfl⟩, (snd X Y).left z, ?_⟩, fun ⟨_, b, hb⟩ ↦ ?_⟩
  · rw [Over.snd_left] at h
    rw [h, Over.comp_left, Scheme.Hom.comp_apply]
    congr 1
    exact Subsingleton.elim (α := Spec (.of K)) _ _
  · rw [Over.snd_left, ← hb, Over.comp_left, Scheme.Hom.comp_apply]
    congr 1
    exact Subsingleton.elim (α := Spec (.of K)) _ _

/-- Let `f : X ⟶ Y` and `g : Y ⟶ S` with `f ≫ g` proper and `g` separated and locally of finite
type. If `f` has finite image on the fibre of `f ≫ g` over `s`, then the same holds over every
point of a neighbourhood of `s`. This is a consequence of Zariski's main theorem. -/
theorem exists_forall_finite_image_preimage_of_finite_image_preimage
    {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S) (s : S)
    (H : (f '' ((f ≫ g) ⁻¹' {s})).Finite)
    [IsProper (f ≫ g)] [IsSeparated g] [LocallyOfFiniteType g] :
    ∃ U : S.Opens, s ∈ U ∧ ∀ t ∈ U, (f '' ((f ≫ g) ⁻¹' {t})).Finite := by
  obtain ⟨U, hsU, hU⟩ :=
    exists_finite_imageι_comp_morphismRestrict_of_finite_image_preimage f g s H
  refine ⟨U, hsU, fun t ht ↦ ?_⟩
  obtain ⟨t, rfl⟩ : t ∈ Set.range U.ι := by rwa [Scheme.Opens.range_ι]
  let h := f.imageι ≫ g
  refine (((h ∣_ U).finite_preimage_singleton t).image ((h ⁻¹ᵁ U).ι ≫ f.imageι)).subset ?_
  rintro _ ⟨x, hx, rfl⟩
  have hhx : h (f.toImage x) = U.ι t := by
    rw [← hx, ← Scheme.Hom.comp_apply, Scheme.Hom.toImage_imageι_assoc]
  obtain ⟨x', hx'⟩ : f.toImage x ∈ Set.range (h ⁻¹ᵁ U).ι := by
    rwa [Scheme.Opens.range_ι, SetLike.mem_coe, Scheme.Hom.mem_preimage, hhx]
  refine ⟨x', U.ι.isOpenEmbedding.injective ?_, ?_⟩
  · rw [← Scheme.Hom.comp_apply, morphismRestrict_ι, Scheme.Hom.comp_apply, hx', hhx]
  · rw [Scheme.Hom.comp_apply, hx', ← Scheme.Hom.comp_apply, Scheme.Hom.toImage_imageι]

/-- **The rigidity lemma** over an algebraically closed field `K`. Let `X` be proper over `K`, `Y`
locally of finite type over `K` with `X × Y` integral, and `Z` separated and locally of finite
type over `K`. If `f : X × Y ⟶ Z` sends the fibre `X × {y₀}` over a `K`-point `y₀` of `Y` to a
single `K`-point `z₀` of `Z`, then `f (x, y) = f (x₀, y)` for any `K`-point `x₀` of `X`. -/
theorem eq_snd_comp_lift_comp_of_isAlgClosed [IsAlgClosed K] {X Y Z : Over (Spec (.of K))}
    [IsProper X.hom] [LocallyOfFiniteType Y.hom] [IsIntegral (X ⊗ Y).left]
    [IsSeparated Z.hom] [LocallyOfFiniteType Z.hom]
    (f : X ⊗ Y ⟶ Z) (x₀ : 𝟙_ _ ⟶ X) (y₀ : 𝟙_ _ ⟶ Y) (z₀ : 𝟙_ _ ⟶ Z)
    (hf : lift (𝟙 X) (toUnit X ≫ y₀) ≫ f = toUnit X ≫ z₀) :
    f = snd X Y ≫ lift (toUnit Y ≫ x₀) (𝟙 Y) ≫ f := by
  let point : Spec (.of K) := IsLocalRing.closedPoint K
  let γ : X ⊗ Y ⟶ Y ⊗ Z := lift (snd X Y) f
  have hγ : γ.left ≫ (fst Y Z).left = (snd X Y).left := by
    rw [← Over.comp_left, lift_fst]
  have : IsProper (snd X Y).left := by dsimp; infer_instance
  have : IsProper (γ.left ≫ (fst Y Z).left) := by rw [hγ]; infer_instance
  have : IsSeparated (fst Y Z).left := by dsimp; infer_instance
  have : LocallyOfFiniteType (fst Y Z).left := by dsimp; infer_instance
  have : IsProper γ.left := .of_comp _ (fst Y Z).left
  have : LocallyOfFiniteType (X ⊗ Y).hom := by dsimp; infer_instance
  have : JacobsonSpace (X ⊗ Y).left := LocallyOfFiniteType.jacobsonSpace (X ⊗ Y).hom
  -- For a `K`-point `y` of `Y`, the map `(x, y') ↦ (x, y)` factors through `x ↦ (x, y)`.
  have hfibre (y : 𝟙_ _ ⟶ Y) :
      X ◁ (toUnit Y ≫ y) = fst X Y ≫ lift (𝟙 X) (toUnit X ≫ y) := by
    ext1 <;> simp
  -- The fibre of `X × Y ⟶ Y` over `y₀` is sent by `γ` to the single point `(y₀, z₀)`.
  have H : (γ.left '' ((γ.left ≫ (fst Y Z).left) ⁻¹' {y₀.left point})).Finite := by
    rw [hγ, preimage_snd_left_eq_range_whiskerLeft_left, ← Set.range_comp, ← TopCat.coe_comp,
      ← Scheme.Hom.comp_base, ← Over.comp_left]
    have : X ◁ (toUnit Y ≫ y₀) ≫ γ = toUnit (X ⊗ Y) ≫ lift y₀ z₀ := by
      ext1
      · simp [γ]
      · rw [Category.assoc, lift_snd, hfibre, Category.assoc, hf]
        simp
    rw [this, Over.comp_left, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
    have : Finite (𝟙_ (Over (Spec (.of K)))).left :=
      have : Subsingleton (𝟙_ (Over (Spec (.of K)))).left :=
        inferInstanceAs (Subsingleton (Spec (.of K)))
      Finite.of_subsingleton
    exact (Set.finite_range _).subset (Set.image_subset_range _ _)
  -- By Zariski's main theorem, `γ` has finite image on the fibres over a neighbourhood `U`
  -- of `y₀`.
  obtain ⟨U, hy₀U, hU⟩ := exists_forall_finite_image_preimage_of_finite_image_preimage
    γ.left (fst Y Z).left (y₀.left point) H
  rw [hγ] at hU
  -- It suffices to compare both sides at the closed points of the dense open `pr₂⁻¹ U`.
  ext1
  have : LocallyOfFiniteType (f.left ≫ Z.hom) := by rw [Over.w]; infer_instance
  refine ext_of_apply_eq Z.hom _ ((snd X Y).left ⁻¹ᵁ U).isOpen.isLocallyClosed
    (((snd X Y).left ⁻¹ᵁ U).isOpen.dense ⟨(lift x₀ y₀).left point, ?_⟩) ?_
    ((Over.w _).trans (Over.w _).symm)
  · rwa [SetLike.mem_coe, Scheme.Hom.mem_preimage, ← Scheme.Hom.comp_apply, ← Over.comp_left,
      lift_snd]
  intro z hzU hz
  have hy : IsClosed {(snd X Y).left z} := by
    simpa using (snd X Y).left.isClosedMap _ hz
  let y : 𝟙_ _ ⟶ Y := Over.homMk (pointOfClosedPoint Y.hom _ hy) (by simp)
  have hyz : y.left point = (snd X Y).left z := pointOfClosedPoint_apply _ _ _ _
  -- The point `(x₀, y)` of the fibre `X × {y}` through `z`.
  let ze : (X ⊗ Y).left := (snd X Y ≫ lift (toUnit Y ≫ x₀) (𝟙 Y)).left z
  -- The fibre `X × {y}` is irreducible and has finite image under `γ`, so `γ` is constant on it.
  have hγz : γ.left z = γ.left ze := by
    have hT : (snd X Y).left ⁻¹' {(snd X Y).left z} = Set.range (X ◁ (toUnit Y ≫ y)).left := by
      rw [← hyz, preimage_snd_left_eq_range_whiskerLeft_left]
    refine subsingleton_image_closure_of_finite_of_isPreirreducible
      (hy.preimage (snd X Y).left.continuous).isLocallyClosed ?_ γ.left.continuous
      γ.left.isClosedMap (hU _ hzU) ⟨z, subset_closure rfl, rfl⟩ ⟨ze, subset_closure ?_, rfl⟩
    · rw [hT, ← Set.image_univ]
      exact ((IrreducibleSpace.isIrreducible_univ _).image _
        (X ◁ (toUnit Y ≫ y)).left.continuous.continuousOn).isPreirreducible
    · simp only [ze, Set.mem_preimage, Set.mem_singleton_iff, ← Scheme.Hom.comp_apply,
        ← Over.comp_left, Category.assoc, lift_snd, Category.comp_id]
  have := congr((snd Y Z).left $hγz)
  rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ← Over.comp_left, lift_snd] at this
  rw [this, ← Scheme.Hom.comp_apply, ← Over.comp_left, Category.assoc]

/-- **The rigidity lemma.** Let `X` be proper and geometrically integral over a field `K`, `Y`
geometrically integral and locally of finite type over `K`, and `Z` separated and locally of
finite type over `K`. If `f : X × Y ⟶ Z` sends the fibre `X × {y₀}` over a `K`-point `y₀` of `Y`
to a single `K`-point `z₀` of `Z`, then `f` factors through the projection to `Y`:
`f (x, y) = f (x₀, y)` for any `K`-point `x₀` of `X`. -/
theorem eq_snd_comp_lift_comp {X Y Z : Over (Spec (.of K))}
    [IsProper X.hom] [GeometricallyIntegral X.hom]
    [LocallyOfFiniteType Y.hom] [GeometricallyIntegral Y.hom]
    [IsSeparated Z.hom] [LocallyOfFiniteType Z.hom]
    (f : X ⊗ Y ⟶ Z) (x₀ : 𝟙_ _ ⟶ X) (y₀ : 𝟙_ _ ⟶ Y) (z₀ : 𝟙_ _ ⟶ Z)
    (hf : lift (𝟙 X) (toUnit X ≫ y₀) ≫ f = toUnit X ≫ z₀) :
    f = snd X Y ≫ lift (toUnit Y ≫ x₀) (𝟙 Y) ≫ f := by
  -- Base change to an algebraic closure of `K`, which is faithful on schemes over `K`, and
  -- transport the hypothesis and conclusion through its monoidal structure.
  let p := Spec.map (CommRingCat.ofHom <| algebraMap K (AlgebraicClosure K))
  let F := Over.pullback p
  have : IsProper (F.obj X).hom := by dsimp [F]; infer_instance
  have : LocallyOfFiniteType (F.obj Y).hom := by dsimp [F]; infer_instance
  have : IsIntegral (F.obj X ⊗ F.obj Y).left := by dsimp [F]; infer_instance
  have : IsSeparated (F.obj Z).hom := by dsimp [F]; infer_instance
  have : LocallyOfFiniteType (F.obj Z).hom := by dsimp [F]; infer_instance
  have H := eq_snd_comp_lift_comp_of_isAlgClosed (Functor.LaxMonoidal.μ F X Y ≫ F.map f)
    (Functor.LaxMonoidal.ε F ≫ F.map x₀) (Functor.LaxMonoidal.ε F ≫ F.map y₀)
    (Functor.LaxMonoidal.ε F ≫ F.map z₀) (by
      rw [← Category.assoc, ← F.map_id, Functor.Monoidal.toUnit_ε_assoc, ← F.map_comp,
        Functor.Monoidal.lift_μ, ← F.map_comp, hf, F.map_comp,
        Functor.Monoidal.toUnit_ε_assoc])
  apply F.map_injective
  rw [← cancel_epi (Functor.LaxMonoidal.μ F X Y), H]
  rw [F.map_comp, F.map_comp, Functor.Monoidal.μ_snd_assoc, ← Functor.Monoidal.lift_μ,
    F.map_comp, ← Functor.Monoidal.toUnit_ε_assoc, F.map_id, Category.assoc]

end AlgebraicGeometry

end TauCeti
