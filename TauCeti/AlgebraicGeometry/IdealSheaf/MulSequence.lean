/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.IdealSheaf.MayerVietoris
public import TauCeti.AlgebraicGeometry.IdealSheaf.TensorProduct

/-!
# The exact sequence of a product of ideal sheaves

Let `I` and `J` be ideal sheaves on a scheme `X`. The closed subscheme `V(I * J)` contains `V(J)`,
and the kernel of the restriction `𝒪_{V(I * J)} ⟶ 𝒪_{V(J)}` is `J ⧸ I J`, which is
`J ⊗ 𝒪_X ⧸ I` because tensoring with `J` is right exact. This gives the short exact sequence of
`𝒪_X`-modules

`0 ⟶ J ⊗ ι_* 𝒪_{V(I)} ⟶ ι_* 𝒪_{V(I * J)} ⟶ ι_* 𝒪_{V(J)} ⟶ 0`

(`Scheme.IdealSheafData.mulSequence` and `Scheme.IdealSheafData.shortExact_mulSequence`), whose
first map is multiplication by local functions of `J`
(`Scheme.IdealSheafData.mulPushforwardSubscheme`) and whose second map is restriction of
functions. When `I` and `J` are the ideal sheaves of effective Cartier divisors `E` and `D`, so
that `V(I * J)` is the divisor `D + E` and `J = 𝒪_X(-D)` is invertible, this is the sequence
`0 ⟶ 𝒪_E(-D) ⟶ 𝒪_{D + E} ⟶ 𝒪_D ⟶ 0`, through which Euler characteristics, and hence degrees of
line bundles, on the nonreduced curve `D + E` are computed from those on `D` and `E`. No
hypothesis on `X`, `I` or `J` is needed.

The first map is a monomorphism because multiplication `I ⊗ J ⟶ I * J` is an epimorphism
(`Scheme.IdealSheafData.epi_sheafMul`): a local function of `J` restricting to zero on
`V(I * J)` lies in `I * J`, hence comes from `J ⊗ I`. The proofs work with morphisms up to
refinements of their sources, as in an arbitrary abelian category.

## References

* The Stacks Project, *Divisors*, Section *Effective Cartier divisors* (Tag 01WQ): the sum
  `D + E` is cut out by the product of the ideal sheaves.
* [The Stacks Project, Section 33.44, Tag 0AYQ](https://stacks.math.columbia.edu/tag/0AYQ):
  degrees on proper curves, computed through exact sequences of this kind.
-/

public section

open CategoryTheory Limits MonoidalCategory

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

noncomputable section

variable {X : Scheme.{u}} (I J : X.IdealSheafData)

/-- The ideal sequence `0 ⟶ I ⟶ 𝒪_X ⟶ ι_* 𝒪_{V(I)} ⟶ 0` tensored on the left with `J`. -/
private abbrev tensorIdealSequence : ShortComplex X.Modules :=
  (ShortComplex.mk _ _ I.sheafι_toPushforwardSubscheme).map (tensorLeft J.sheaf)

private lemma tensorIdealSequence_f :
    (tensorIdealSequence I J).f = J.sheaf ◁ I.sheafιUnit :=
  rfl

private lemma tensorIdealSequence_g :
    (tensorIdealSequence I J).g = J.sheaf ◁ I.toPushforwardSubscheme :=
  rfl

/-- Multiplication `J ⊗ 𝒪_X ⟶ 𝒪_X` by the local functions of `J`. -/
private abbrev tensorMul : J.sheaf ⊗ 𝟙_ X.Modules ⟶ 𝟙_ X.Modules :=
  (ρ_ J.sheaf).hom ≫ J.sheafιUnit

/-- Multiplication `J ⊗ I ⟶ 𝒪_X` of local functions factors through `I * J`. -/
private lemma braiding_sheafMul_sheafιUnit :
    (β_ J.sheaf I.sheaf).hom ≫ sheafMul I J ≫ (I * J).sheafιUnit =
      (tensorIdealSequence I J).f ≫ tensorMul J := by
  rw [sheafMul_sheafιUnit, ← BraidedCategory.braiding_naturality_assoc, braiding_leftUnitor,
    tensorHom_def', Category.assoc, rightUnitor_naturality, tensorIdealSequence_f]

private lemma tensorIdealSequence_f_tensorMul_toPushforwardSubscheme :
    (tensorIdealSequence I J).f ≫ tensorMul J ≫ (I * J).toPushforwardSubscheme = 0 := by
  rw [← Category.assoc, ← braiding_sheafMul_sheafιUnit, Category.assoc, Category.assoc,
    sheafιUnit_def, sheafι_toPushforwardSubscheme, comp_zero, comp_zero]

/-- Tensoring with `J` is right exact, being left adjoint to the internal Hom out of `J`, so the
tensored sequence is exact and ends in an epimorphism. -/
private lemma epi_tensorIdealSequence_g : Epi (tensorIdealSequence I J).g :=
  Functor.map_epi (tensorLeft J.sheaf) I.toPushforwardSubscheme

private lemma exact_tensorIdealSequence : (tensorIdealSequence I J).Exact := by
  have : PreservesColimitsOfSize.{0, 0} (tensorLeft J.sheaf) :=
    (ihom.adjunction J.sheaf).leftAdjoint_preservesColimits
  exact I.shortExact_toPushforwardSubscheme.exact.map_of_epi_of_preservesCokernel
    (tensorLeft J.sheaf) inferInstance inferInstance

/-- `J ⊗ ι_* 𝒪_{V(I)}` is the cokernel of `J ⊗ I ⟶ J ⊗ 𝒪_X`. -/
private def tensorIdealSequenceIsCokernel :
    IsColimit (CokernelCofork.ofπ _ (tensorIdealSequence I J).zero) :=
  have := epi_tensorIdealSequence_g I J
  (exact_tensorIdealSequence I J).gIsCokernel

/-- Multiplication `J ⊗ ι_* 𝒪_{V(I)} ⟶ ι_* 𝒪_{V(I * J)}` by the local functions of the ideal
sheaf `J`: a function on `V(I)` times a local function of `J` is well defined on `V(I * J)`
(`whiskerLeft_toPushforwardSubscheme_mulPushforwardSubscheme`). -/
def mulPushforwardSubscheme :
    J.sheaf ⊗ I.pushforwardSubscheme ⟶ (I * J).pushforwardSubscheme :=
  (CokernelCofork.IsColimit.desc' (tensorIdealSequenceIsCokernel I J)
    (tensorMul J ≫ (I * J).toPushforwardSubscheme)
    (tensorIdealSequence_f_tensorMul_toPushforwardSubscheme I J)).val

/-- Multiplying the restriction to `V(I)` of a local function by a local function of `J` is
restricting their product to `V(I * J)`. -/
@[reassoc (attr := simp)]
lemma whiskerLeft_toPushforwardSubscheme_mulPushforwardSubscheme :
    J.sheaf ◁ I.toPushforwardSubscheme ≫ I.mulPushforwardSubscheme J =
      (ρ_ J.sheaf).hom ≫ J.sheafιUnit ≫ (I * J).toPushforwardSubscheme := by
  rw [← Category.assoc]
  exact (CokernelCofork.IsColimit.desc' (tensorIdealSequenceIsCokernel I J)
    (tensorMul J ≫ (I * J).toPushforwardSubscheme)
    (tensorIdealSequence_f_tensorMul_toPushforwardSubscheme I J)).property

/-- **The exact sequence of a product of ideal sheaves**
`J ⊗ ι_* 𝒪_{V(I)} ⟶ ι_* 𝒪_{V(I * J)} ⟶ ι_* 𝒪_{V(J)}` of two ideal sheaves `I` and `J`. The first
map multiplies by the local functions of `J`, the second restricts functions to `V(J)`. It is
short exact (`shortExact_mulSequence`). -/
@[expose] def mulSequence : ShortComplex X.Modules where
  f := I.mulPushforwardSubscheme J
  g := pushforwardSubschemeMap (mul_le_of_le_one_left bot_le le_top)
  zero := by
    have := epi_tensorIdealSequence_g I J
    rw [← cancel_epi (tensorIdealSequence I J).g, comp_zero, tensorIdealSequence_g,
      whiskerLeft_toPushforwardSubscheme_mulPushforwardSubscheme_assoc,
      toPushforwardSubscheme_pushforwardSubschemeMap, sheafιUnit_def,
      sheafι_toPushforwardSubscheme, comp_zero]

/-- The first term of the sequence of a product of ideal sheaves is `J ⊗ ι_* 𝒪_{V(I)}`. -/
@[simp]
lemma mulSequence_X₁ : (mulSequence I J).X₁ = J.sheaf ⊗ I.pushforwardSubscheme :=
  rfl

/-- The middle term of the sequence of a product of ideal sheaves is `ι_* 𝒪_{V(I * J)}`. -/
@[simp]
lemma mulSequence_X₂ : (mulSequence I J).X₂ = (I * J).pushforwardSubscheme :=
  rfl

/-- The last term of the sequence of a product of ideal sheaves is `ι_* 𝒪_{V(J)}`. -/
@[simp]
lemma mulSequence_X₃ : (mulSequence I J).X₃ = J.pushforwardSubscheme :=
  rfl

/-- The first map of the sequence of a product of ideal sheaves is multiplication by `J`. -/
@[simp]
lemma mulSequence_f : (mulSequence I J).f = I.mulPushforwardSubscheme J :=
  rfl

/-- The second map of the sequence of a product of ideal sheaves is the restriction to `V(J)`. -/
@[simp]
lemma mulSequence_g :
    (mulSequence I J).g = pushforwardSubschemeMap (mul_le_of_le_one_left bot_le le_top) :=
  rfl

/-- Multiplication `J ⊗ ι_* 𝒪_{V(I)} ⟶ ι_* 𝒪_{V(I * J)}` is a monomorphism: a function on `V(I)`
whose product with `J` vanishes on `V(I * J)` vanishes on `V(I)`. -/
instance mono_mulPushforwardSubscheme : Mono (I.mulPushforwardSubscheme J) := by
  have hIJ := (I * J).shortExact_toPushforwardSubscheme
  have := epi_tensorIdealSequence_g I J
  have := epi_sheafMul I J
  refine Preadditive.mono_of_cancel_zero _ fun {T} x hx ↦ ?_
  -- Lift `x` to `J ⊗ 𝒪_X` after refining its source.
  obtain ⟨T₁, π₁, _, u, hu⟩ := surjective_up_to_refinements_of_epi (tensorIdealSequence I J).g x
  -- Its product with `J` restricts to zero on `V(I * J)`, so it is a section of `I * J` ...
  have hu' : (u ≫ tensorMul J) ≫ (I * J).toPushforwardSubscheme = 0 := by
    have h := u ≫= whiskerLeft_toPushforwardSubscheme_mulPushforwardSubscheme I J
    rw [← Category.assoc, ← tensorIdealSequence_g, ← hu, Category.assoc, hx, comp_zero] at h
    simpa only [Category.assoc] using h.symm
  -- ... which, after a further refinement, is a product of sections of `J` and of `I`.
  obtain ⟨T₂, π₂, _, w, hw⟩ := surjective_up_to_refinements_of_epi (sheafMul I J)
    (hIJ.exact.lift _ hu')
  have hwu : (w ≫ (β_ J.sheaf I.sheaf).inv) ≫ (tensorIdealSequence I J).f = π₂ ≫ u := by
    rw [← cancel_mono (tensorMul J), Category.assoc, Category.assoc,
      ← braiding_sheafMul_sheafιUnit, Iso.inv_hom_id_assoc, ← Category.assoc, ← hw,
      Category.assoc, Category.assoc]
    exact congrArg (π₂ ≫ ·) (hIJ.exact.lift_f _ hu')
  rw [← cancel_epi π₁, ← cancel_epi π₂, comp_zero, comp_zero, hu, ← Category.assoc, ← hwu,
    Category.assoc, (tensorIdealSequence I J).zero, comp_zero]

/-- The sequence of a product of ideal sheaves is exact in the middle: a function on `V(I * J)`
vanishing on `V(J)` is, locally, a local function of `J`. -/
private lemma exact_mulSequence : (mulSequence I J).Exact := by
  have hJs := J.shortExact_toPushforwardSubscheme
  rw [ShortComplex.exact_iff_exact_up_to_refinements]
  dsimp only [mulSequence_X₁, mulSequence_X₂, mulSequence_X₃, mulSequence_f, mulSequence_g]
  intro A y hy
  -- Lift `y` to `𝒪_X` after refining `A`.
  obtain ⟨A₁, π₁, _, a, ha⟩ :=
    surjective_up_to_refinements_of_epi (I * J).toPushforwardSubscheme y
  -- The lift vanishes on `V(J)`, so it is a section of `J`.
  have ha' : a ≫ J.toPushforwardSubscheme = 0 := by
    rw [← toPushforwardSubscheme_pushforwardSubschemeMap (I := I * J) (J := J)
      (mul_le_of_le_one_left bot_le le_top), ← Category.assoc, ← ha, Category.assoc]
    exact (congrArg (π₁ ≫ ·) hy).trans comp_zero
  obtain ⟨c, hc⟩ : ∃ c : A₁ ⟶ J.sheaf, c ≫ J.sheafιUnit = a := ⟨_, hJs.exact.lift_f a ha'⟩
  refine ⟨A₁, π₁, inferInstance, c ≫ (ρ_ J.sheaf).inv ≫ J.sheaf ◁ I.toPushforwardSubscheme, ?_⟩
  rw [ha, Category.assoc, Category.assoc,
    whiskerLeft_toPushforwardSubscheme_mulPushforwardSubscheme, Iso.inv_hom_id_assoc,
    reassoc_of% hc]

/-- **The sequence of a product of ideal sheaves is short exact**:
`0 ⟶ J ⊗ ι_* 𝒪_{V(I)} ⟶ ι_* 𝒪_{V(I * J)} ⟶ ι_* 𝒪_{V(J)} ⟶ 0` for all ideal sheaves `I` and
`J`. -/
theorem shortExact_mulSequence : (mulSequence I J).ShortExact where
  mono_f := I.mono_mulPushforwardSubscheme J
  epi_g := epi_pushforwardSubschemeMap _
  exact := exact_mulSequence I J

end

end AlgebraicGeometry.Scheme.IdealSheafData
