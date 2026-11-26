/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Contact.Isotropic
public import TauCeti.Geometry.Symplectic.Rescale
public import TauCeti.LinearAlgebra.SesquilinearForm.SymplecticNormal
import TauCeti.Algebra.Module.Submodule.Map
import TauCeti.Geometry.Manifold.IsManifold.Basic
import TauCeti.LinearAlgebra.Quotient.Basic

/-!
# The conformal symplectic normal spaces of an isotropic map

Let `ξ` be a contact structure on a manifold `M` of dimension `2 m + 1`, with Levi form
`L_ξ : ξ × ξ → TM ⧸ ξ` (`TauCeti.distributionLeviForm`), and let `f : N → M` be a map. At a point
`y` of `N`, let `W = df_y(T_y N) ∩ ξ_(f y)` be the part of the tangent image lying in the contact
hyperplane. The **conformal symplectic normal space** of `f` at `y`
(`TauCeti.ConformalSymplecticNormal J ξ f y`) is the symplectic normal space `W^⊥ ⧸ (W ∩ W^⊥)` of
`W` for the Levi form, where `W^⊥` is the Levi orthogonal of `W` inside `ξ_(f y)`. When `f` is
isotropic, that is horizontal for `ξ`, `W` is the whole tangent image `T_y N` and is isotropic for
the Levi form, so this is `(T_y N)^⊥ ⧸ T_y N`.

The Levi form descends to an alternating form on this space with values in the contact line
`T_(f y) M ⧸ ξ_(f y)` (`TauCeti.conformalSymplecticNormalForm`), and this form is nondegenerate
(`TauCeti.IsContactDistribution.injective_conformalSymplecticNormalForm`). Everything here is
defined from `ξ` alone: no defining one-form or coorientation is chosen, so the construction
applies to contact structures which are not the kernel of any global one-form.

* For an isotropic map with injective differential at `y`, the space has dimension
  `2 (m - dim N)`: `dim + 2 dim N + 1 = dim M`
  (`TauCeti.IsHorizontalMap.finrank_conformalSymplecticNormal_add`).
* It vanishes for Legendrian immersions, and a smooth isotropic immersion from a nonempty manifold
  is Legendrian exactly when all its conformal symplectic normal spaces vanish
  (`TauCeti.isLegendrianImmersion_iff_forall_subsingleton_conformalSymplecticNormal`).

The construction is natural. Let `F : M → M₁` be a `C²` map whose differentials carry `ξ` onto a
distribution `ξ₁` near `f y`, as a contactomorphism between open neighbourhoods of `f(N)` and
`F(f(N))` does. Its differential carries the Levi form of `ξ` to that of `ξ₁`, up to the induced
isomorphism of contact lines `T_(f y) M ⧸ ξ_(f y) → T_(F (f y)) M₁ ⧸ ξ₁_(F (f y))`
(`TauCeti.distributionLeviForm_restrict_mfderiv`). Hence `[u] ↦ [dF u]` is an isomorphism from the
conformal symplectic normal space of `f` onto that of `F ∘ f`
(`TauCeti.conformalSymplecticNormalEquiv`), conformally symplectic for the two line-valued forms
(`TauCeti.conformalSymplecticNormalForm_conformalSymplecticNormalEquiv`), and compatible with
composition (`TauCeti.conformalSymplecticNormalEquiv_trans`).

A local defining form `α` of `ξ` at `f y`, with `ker α_(f y) = ξ_(f y)`, identifies the contact
line with `ℝ` and turns the line-valued form into a linear symplectic form
(`TauCeti.IsContactDistribution.normalSymplecticForm`). If `α` is differentiable at `f y` and
defines `ξ` on a neighbourhood of `f y`, this symplectic form is `[u], [v] ↦ dα(u, v)`
(`TauCeti.IsContactDistribution.normalSymplecticForm_mk_eq_mextDeriv`), so it is the symplectic
normal space of `T_y N` in the symplectic vector space `(ξ_(f y), dα)`. Replacing `α` by `g α`, for
a function `g` not vanishing at `f y`, rescales it by `g (f y)`
(`TauCeti.IsContactDistribution.normalSymplecticForm_fun_smul`). This is the transition law of the
local descriptions, and the reason the normal spaces carry only a conformal class of symplectic
forms, together with the contact line in which it takes values.

## References

* H. Geiges, *An Introduction to Contact Topology*, Cambridge Studies in Advanced Mathematics 109
  (2008), Section 2.5 (the conformal symplectic normal bundle and the isotropic neighbourhood
  theorem).
-/

public section

noncomputable section

open Set Filter Function Module Bundle
open scoped Manifold Topology ContDiff

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  {E' H' N : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} [TopologicalSpace N] [ChartedSpace H' N]
  {D : Π x : M, Submodule ℝ (TangentSpace I x)} {f : N → M} {y : N}

variable [CompleteSpace E] [IsManifold I 2 M]

/-! ### The conformal symplectic normal space and its line-valued form -/

variable (J D f y) in
/-- The **conformal symplectic normal space** of a map `f : N → M` at `y` for a hyperplane field
`D`: the symplectic normal space `W^⊥ ⧸ (W ∩ W^⊥)`, for the Levi form of `D` at `f y`, of the
part `W = df_y(T_y N) ∩ D_(f y)` of the tangent image lying in `D_(f y)`. For a map horizontal
for `D`, `W` is the whole tangent image and this is `(T_y N)^⊥ ⧸ T_y N`. -/
abbrev ConformalSymplecticNormal : Type _ :=
  LinearMap.SymplecticNormal (distributionLeviForm D (f y))
    ((LinearMap.range (mfderiv J I f y).toLinearMap).comap (D (f y)).subtype)

variable (J D f y) in
/-- The alternating form on the conformal symplectic normal space of `f` at `y` induced by the
Levi form of `D`, with values in the line `T_(f y) M ⧸ D_(f y)`: `[u], [v] ↦ L_D (u, v)`. -/
def conformalSymplecticNormalForm :
    ConformalSymplecticNormal J D f y →ₗ[ℝ] ConformalSymplecticNormal J D f y →ₗ[ℝ]
      TangentSpace I (f y) ⧸ D (f y) :=
  isAlt_distributionLeviForm.isRefl.symplecticNormalForm
    ((LinearMap.range (mfderiv J I f y).toLinearMap).comap (D (f y)).subtype)

/-- The defining formula `[u], [v] ↦ L_D (u, v)` of the form on the conformal symplectic normal
space. -/
@[simp]
theorem conformalSymplecticNormalForm_mk
    (u v : ((LinearMap.range (mfderiv J I f y).toLinearMap).comap (D (f y)).subtype).orthogonalBilin
      (distributionLeviForm D (f y))) :
    conformalSymplecticNormalForm J D f y (Submodule.Quotient.mk u) (Submodule.Quotient.mk v) =
      distributionLeviForm D (f y) u v :=
  LinearMap.IsRefl.symplecticNormalForm_mk _ u v

/-- The form on the conformal symplectic normal space is alternating. -/
theorem isAlt_conformalSymplecticNormalForm : (conformalSymplecticNormalForm J D f y).IsAlt :=
  isAlt_distributionLeviForm.isAlt_symplecticNormalForm

/-! ### Naturality under maps carrying one distribution to another -/

section Naturality

variable {E₁ H₁ M₁ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [CompleteSpace E₁]
  [TopologicalSpace H₁] {I₁ : ModelWithCorners ℝ E₁ H₁} [TopologicalSpace M₁] [ChartedSpace H₁ M₁]
  [IsManifold I₁ 2 M₁] {E₂ H₂ M₂ : Type*} [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]
  [CompleteSpace E₂] [TopologicalSpace H₂] {I₂ : ModelWithCorners ℝ E₂ H₂} [TopologicalSpace M₂]
  [ChartedSpace H₂ M₂] [IsManifold I₂ 2 M₂] {k k₁ k₂ : ℕ}
  {D₁ : Π x : M₁, Submodule ℝ (TangentSpace I₁ x)} {D₂ : Π x : M₂, Submodule ℝ (TangentSpace I₂ x)}
  {F : M → M₁} {G : M₁ → M₂}

omit [CompleteSpace E] [IsManifold I 2 M] [CompleteSpace E₁] [IsManifold I₁ 2 M₁] in
/-- The restriction of the invertible differential to an equivalence `D x ≃ D₁ (F x)` agrees with
the restriction of the differential to a map `D x → D₁ (F x)`. -/
private theorem ofSubmodules_ofBijective_mfderiv_apply {x : M}
    (hFx : (mfderiv I I₁ F x).IsInvertible) (hFD : ∀ u ∈ D x, mfderiv I I₁ F x u ∈ D₁ (F x))
    (hmap : (D x).map (LinearEquiv.ofBijective (mfderiv I I₁ F x).toLinearMap hFx.bijective :
      TangentSpace I x →ₗ[ℝ] TangentSpace I₁ (F x)) = D₁ (F x)) (u : D x) :
    (LinearEquiv.ofBijective (mfderiv I I₁ F x).toLinearMap hFx.bijective).ofSubmodules _ _ hmap u =
      (mfderiv I I₁ F x).toLinearMap.restrict hFD u :=
  Subtype.ext (by simp)

omit [CompleteSpace E] [IsManifold I 2 M] [CompleteSpace E₁] [IsManifold I₁ 2 M₁] in
/-- The differential of `F` carries the part of the tangent image of `f` lying in `D` onto the part
of the tangent image of `F ∘ f` lying in `D₁`. -/
private theorem map_comap_range_mfderiv (hFx : (mfderiv I I₁ F (f y)).IsInvertible)
    (hmap : (D (f y)).map (LinearEquiv.ofBijective (mfderiv I I₁ F (f y)).toLinearMap
      hFx.bijective : TangentSpace I (f y) →ₗ[ℝ] TangentSpace I₁ (F (f y))) = D₁ (F (f y)))
    (hFd : MDifferentiableAt I I₁ F (f y)) (hf : MDifferentiableAt J I f y) :
    ((LinearMap.range (mfderiv J I f y).toLinearMap).comap (D (f y)).subtype).map
        ((LinearEquiv.ofBijective (mfderiv I I₁ F (f y)).toLinearMap hFx.bijective).ofSubmodules
          _ _ hmap : D (f y) →ₗ[ℝ] D₁ (F (f y))) =
      (LinearMap.range (mfderiv J I₁ (F ∘ f) y).toLinearMap).comap (D₁ ((F ∘ f) y)).subtype := by
  ext w
  simp [mfderiv_comp y hFd hf, LinearEquiv.eq_symm_apply]

variable (J D f y) in
/-- **The conformal symplectic normal spaces under a map carrying one distribution to another.**
Let `F : M → M₁` be `C²` at `f y`, with invertible differential there, and let `D`, `D₁` be `C¹`
distributions such that `dF_(f y)` maps `D (f y)` into `D₁ (F (f y))`, while near `f y` the inverse
differentials map `D₁ (F z)` into `D z`; a contactomorphism of contact structures between open
neighbourhoods is the main example. Then `[u] ↦ [dF u]` is an isomorphism from the conformal
symplectic normal space of `f` at `y` onto that of `F ∘ f`. It is conformally symplectic: it carries
the line-valued form of `D₁` to the image of the form of `D` under the isomorphism of contact lines
induced by `dF` (`TauCeti.conformalSymplecticNormalForm_conformalSymplecticNormalEquiv`). -/
def conformalSymplecticNormalEquiv {n : ℕ∞ω} (hD : IsContMDiffDistribution I 1 k D)
    (hD₁ : IsContMDiffDistribution I₁ 1 k₁ D₁) (hF : ContMDiffAt I I₁ n F (f y)) (hn : 2 ≤ n)
    (hFx : (mfderiv I I₁ F (f y)).IsInvertible)
    (hFD : ∀ u ∈ D (f y), mfderiv I I₁ F (f y) u ∈ D₁ (F (f y)))
    (hFD' : ∀ᶠ z in 𝓝 (f y), ∀ v ∈ D₁ (F z), (mfderiv I I₁ F z).inverse v ∈ D z)
    (hf : MDifferentiableAt J I f y) :
    ConformalSymplecticNormal J D f y ≃ₗ[ℝ] ConformalSymplecticNormal J D₁ (F ∘ f) y :=
  -- The inverse differential carries `D₁ (F (f y))` back into `D (f y)`.
  have hFD₁ (u) (hu : mfderiv I I₁ F (f y) u ∈ D₁ (F (f y))) : u ∈ D (f y) :=
    hFx.inverse_apply_self u ▸ hFD'.self_of_nhds _ hu
  have hmap : (D (f y)).map (LinearEquiv.ofBijective (mfderiv I I₁ F (f y)).toLinearMap
      hFx.bijective : TangentSpace I (f y) →ₗ[ℝ] TangentSpace I₁ (F (f y))) = D₁ (F (f y)) :=
    Submodule.map_equiv_eq_iff.2 fun u ↦ ⟨hFD₁ u, hFD u⟩
  LinearMap.symplecticNormalCongr _ _
    ((LinearEquiv.ofBijective (mfderiv I I₁ F (f y)).toLinearMap hFx.bijective).ofSubmodules _ _
      hmap)
    (ℓ := (D (f y)).mapQ (D₁ (F (f y))) (mfderiv I I₁ F (f y)).toLinearMap hFD)
    ((Submodule.mapQ_injective_iff _ _ _ hFD).2 hFD₁)
    -- The target distribution is indexed by `(F ∘ f) y`, which `rw` does not unfold to
    -- `F (f y)`, so the restrictions are identified in term mode.
    (fun u v ↦ (congrArg₂ (distributionLeviForm D₁ (F (f y)) · ·)
      (ofSubmodules_ofBijective_mfderiv_apply hFx hFD hmap u)
      (ofSubmodules_ofBijective_mfderiv_apply hFx hFD hmap v)).trans
      (distributionLeviForm_restrict_mfderiv hD hD₁ hF hn hFx hFD hFD' u v))
    (map_comap_range_mfderiv hFx hmap (hF.mdifferentiableAt (two_pos.trans_le hn).ne') hf)

/-- The isomorphism of conformal symplectic normal spaces induced by `F` sends the class of `u` to
the class of `dF u`. -/
theorem conformalSymplecticNormalEquiv_mk {n : ℕ∞ω} (hD : IsContMDiffDistribution I 1 k D)
    (hD₁ : IsContMDiffDistribution I₁ 1 k₁ D₁) (hF : ContMDiffAt I I₁ n F (f y)) (hn : 2 ≤ n)
    (hFx : (mfderiv I I₁ F (f y)).IsInvertible)
    (hFD : ∀ u ∈ D (f y), mfderiv I I₁ F (f y) u ∈ D₁ (F (f y)))
    (hFD' : ∀ᶠ z in 𝓝 (f y), ∀ v ∈ D₁ (F z), (mfderiv I I₁ F z).inverse v ∈ D z)
    (hf : MDifferentiableAt J I f y)
    (u : ((LinearMap.range (mfderiv J I f y).toLinearMap).comap (D (f y)).subtype).orthogonalBilin
      (distributionLeviForm D (f y)))
    (u' : ((LinearMap.range (mfderiv J I₁ (F ∘ f) y).toLinearMap).comap
      (D₁ ((F ∘ f) y)).subtype).orthogonalBilin (distributionLeviForm D₁ ((F ∘ f) y)))
    (hu : ((u' : D₁ ((F ∘ f) y)) : TangentSpace I₁ ((F ∘ f) y)) =
      mfderiv I I₁ F (f y) ((u : D (f y)) : TangentSpace I (f y))) :
    conformalSymplecticNormalEquiv J D f y hD hD₁ hF hn hFx hFD hFD' hf
        (Submodule.Quotient.mk u) = Submodule.Quotient.mk u' := by
  rw [conformalSymplecticNormalEquiv]
  exact (LinearMap.symplecticNormalCongr_mk _ _ _ u).trans
    (congrArg _ (Subtype.ext (Subtype.ext hu.symm)))

/-- **The isomorphism of conformal symplectic normal spaces is conformally symplectic.** The
isomorphism induced by `F` carries the line-valued form of `D₁` on the conformal symplectic normal
space of `F ∘ f` to the image of the form of `D` under the map of contact lines
`T_(f y) M ⧸ D (f y) → T_(F (f y)) M₁ ⧸ D₁ (F (f y))` induced by `dF`. -/
theorem conformalSymplecticNormalForm_conformalSymplecticNormalEquiv {n : ℕ∞ω}
    (hD : IsContMDiffDistribution I 1 k D) (hD₁ : IsContMDiffDistribution I₁ 1 k₁ D₁)
    (hF : ContMDiffAt I I₁ n F (f y)) (hn : 2 ≤ n) (hFx : (mfderiv I I₁ F (f y)).IsInvertible)
    (hFD : ∀ u ∈ D (f y), mfderiv I I₁ F (f y) u ∈ D₁ (F (f y)))
    (hFD' : ∀ᶠ z in 𝓝 (f y), ∀ v ∈ D₁ (F z), (mfderiv I I₁ F z).inverse v ∈ D z)
    (hf : MDifferentiableAt J I f y) (a b : ConformalSymplecticNormal J D f y) :
    conformalSymplecticNormalForm J D₁ (F ∘ f) y
        (conformalSymplecticNormalEquiv J D f y hD hD₁ hF hn hFx hFD hFD' hf a)
        (conformalSymplecticNormalEquiv J D f y hD hD₁ hF hn hFx hFD hFD' hf b) =
      (D (f y)).mapQ (D₁ (F (f y))) (mfderiv I I₁ F (f y)).toLinearMap hFD
        (conformalSymplecticNormalForm J D f y a b) :=
  LinearMap.IsRefl.symplecticNormalForm_symplecticNormalCongr _ _ _ _ _ a b

/-- **Naturality is compatible with composition.** For maps `F : M → M₁` and `G : M₁ → M₂` carrying
`D` to `D₁` and `D₁` to `D₂` near `f y` and `F (f y)`, the isomorphism of conformal symplectic
normal spaces induced by `G ∘ F` is the composite of those induced by `F` and by `G`. -/
theorem conformalSymplecticNormalEquiv_trans {n n₁ n₂ : ℕ∞ω}
    (hD : IsContMDiffDistribution I 1 k D) (hD₁ : IsContMDiffDistribution I₁ 1 k₁ D₁)
    (hD₂ : IsContMDiffDistribution I₂ 1 k₂ D₂) (hF : ContMDiffAt I I₁ n F (f y)) (hn : 2 ≤ n)
    (hFx : (mfderiv I I₁ F (f y)).IsInvertible)
    (hFD : ∀ u ∈ D (f y), mfderiv I I₁ F (f y) u ∈ D₁ (F (f y)))
    (hFD' : ∀ᶠ z in 𝓝 (f y), ∀ v ∈ D₁ (F z), (mfderiv I I₁ F z).inverse v ∈ D z)
    (hG : ContMDiffAt I₁ I₂ n₁ G (F (f y))) (hn₁ : 2 ≤ n₁)
    (hGx : (mfderiv I₁ I₂ G (F (f y))).IsInvertible)
    (hGD : ∀ u ∈ D₁ (F (f y)), mfderiv I₁ I₂ G (F (f y)) u ∈ D₂ (G (F (f y))))
    (hGD' : ∀ᶠ z in 𝓝 (F (f y)), ∀ v ∈ D₂ (G z), (mfderiv I₁ I₂ G z).inverse v ∈ D₁ z)
    (hGF : ContMDiffAt I I₂ n₂ (G ∘ F) (f y)) (hn₂ : 2 ≤ n₂)
    (hGFx : (mfderiv I I₂ (G ∘ F) (f y)).IsInvertible)
    (hGFD : ∀ u ∈ D (f y), mfderiv I I₂ (G ∘ F) (f y) u ∈ D₂ (G (F (f y))))
    (hGFD' : ∀ᶠ z in 𝓝 (f y), ∀ v ∈ D₂ (G (F z)), (mfderiv I I₂ (G ∘ F) z).inverse v ∈ D z)
    (hf : MDifferentiableAt J I f y) :
    (conformalSymplecticNormalEquiv J D f y hD hD₁ hF hn hFx hFD hFD' hf).trans
        (conformalSymplecticNormalEquiv J D₁ (F ∘ f) y hD₁ hD₂ hG hn₁ hGx hGD hGD'
          ((hF.mdifferentiableAt (two_pos.trans_le hn).ne').comp y hf)) =
      conformalSymplecticNormalEquiv J D f y hD hD₂ hGF hn₂ hGFx hGFD hGFD' hf := by
  ext a
  induction a using Submodule.Quotient.induction_on with
  | H u =>
    have hcomp : mfderiv I I₂ (G ∘ F) (f y) = (mfderiv I₁ I₂ G (F (f y))).comp
        (mfderiv I I₁ F (f y)) :=
      mfderiv_comp (f y) (hG.mdifferentiableAt (two_pos.trans_le hn₁).ne')
        (hF.mdifferentiableAt (two_pos.trans_le hn).ne')
    rw [LinearEquiv.trans_apply, conformalSymplecticNormalEquiv, conformalSymplecticNormalEquiv,
      conformalSymplecticNormalEquiv]
    -- The base points `G ((F ∘ f) y)` and `(G ∘ F ∘ f) y` agree only up to unfolding `∘`, which
    -- `rw` does not see through; the formula for the classes is applied in term mode instead.
    refine ((congrArg _ (LinearMap.symplecticNormalCongr_mk _ _ _ u)).trans
      (LinearMap.symplecticNormalCongr_mk _ _ _ _)).trans
      ((congrArg _ (Subtype.ext (Subtype.ext ?_))).trans
        (LinearMap.symplecticNormalCongr_mk _ _ _ u).symm)
    simp [hcomp]

end Naturality

variable [FiniteDimensional ℝ E] {n : ℕ∞ω}

/-- **The form on the conformal symplectic normal space of a contact structure is
nondegenerate**: `[u] ↦ L_D (u, ·)` is injective, for any map `f`. -/
theorem IsContactDistribution.injective_conformalSymplecticNormalForm
    (hD : IsContactDistribution I n D) : Injective (conformalSymplecticNormalForm J D f y) :=
  have : FiniteDimensional ℝ (TangentSpace I (f y)) := inferInstanceAs (FiniteDimensional ℝ E)
  isAlt_distributionLeviForm.isRefl.injective_symplecticNormalForm
    (hD.bijective_distributionLeviForm (f y)).injective (hD.finrank_quotient (f y))

/-! ### Isotropic and Legendrian maps -/

section Isotropic

variable [IsManifold J 2 N]

/-- **Dimension of the conformal symplectic normal space.** Let `D` be a `C^n` contact structure,
with `1 ≤ n`, on a manifold of dimension `2 m + 1`, and let `f` be horizontal for `D`, of class
`C²` at `y` and with injective differential at `y`. Then its conformal symplectic normal space at
`y` has dimension `2 (m - dim N)`: `dim + 2 dim N + 1 = dim M`. -/
theorem IsHorizontalMap.finrank_conformalSymplecticNormal_add [IsManifold I (n + 1) M]
    (hD : IsContactDistribution I n D) (hn : 1 ≤ n) (hf : IsHorizontalMap J D f)
    (hfy : ContMDiffAt J I 2 f y) (hinj : Injective (mfderiv J I f y)) :
    finrank ℝ (ConformalSymplecticNormal J D f y) + 2 * finrank ℝ E' + 1 = finrank ℝ E := by
  have : FiniteDimensional ℝ (TangentSpace I (f y)) := inferInstanceAs (FiniteDimensional ℝ E)
  set W := (LinearMap.range (mfderiv J I f y).toLinearMap).comap (D (f y)).subtype
  have hdim : finrank ℝ (ConformalSymplecticNormal J D f y) + 2 * finrank ℝ W =
      finrank ℝ (D (f y)) :=
    LinearMap.finrank_symplecticNormal_add_two_mul_finrank
      (hD.bijective_distributionLeviForm (f y)).injective (hD.finrank_quotient (f y))
      (hf.le_orthogonalBilin hD hn hfy)
  -- The tangent image has the dimension of `N`, since the differential is injective.
  have hW : finrank ℝ W = finrank ℝ E' := by
    rw [LinearEquiv.finrank_eq (Submodule.comapSubtypeEquivOfLe (hf.range_mfderiv_le y)),
      LinearMap.finrank_range_of_inj hinj]
    exact finrank_tangentSpace y
  have := hD.finrank_add_one (f y)
  omega

/-- **Legendrian immersions have zero conformal symplectic normal spaces.** -/
theorem IsLegendrianImmersion.subsingleton_conformalSymplecticNormal
    (h : IsLegendrianImmersion J D f) (y : N) :
    Subsingleton (ConformalSymplecticNormal J D f y) := by
  have : IsManifold I (1 + 1) M := .of_le (n := 2) (by norm_num)
  have := h.isHorizontalMap.finrank_conformalSymplecticNormal_add h.isContactDistribution le_rfl
    ((h.isImmersion.contMDiff y).of_le (by simp)) (h.isImmersion.mfderiv_injective (by simp) y)
  have h2 := h.two_mul_finrank_add_one
  exact finrank_zero_iff (R := ℝ) |>.1 (by omega)

/-- **Legendrian immersions are the isotropic immersions with zero conformal symplectic normal
spaces.** A smooth immersion from a nonempty manifold, horizontal for a contact structure `D`, is a
Legendrian immersion exactly when all its conformal symplectic normal spaces are zero. -/
theorem isLegendrianImmersion_iff_forall_subsingleton_conformalSymplecticNormal [Nonempty N]
    [IsManifold I (n + 1) M] (hD : IsContactDistribution I n D) (hn : 1 ≤ n)
    (hf : Manifold.IsImmersion J I ∞ f) (hfD : IsHorizontalMap J D f) :
    IsLegendrianImmersion J D f ↔ ∀ y, Subsingleton (ConformalSymplecticNormal J D f y) := by
  refine ⟨fun h ↦ h.subsingleton_conformalSymplecticNormal, fun h ↦ ?_⟩
  rw [isLegendrianImmersion_iff_finrank_le hD hn hf hfD]
  obtain ⟨y⟩ := ‹Nonempty N›
  have := hfD.finrank_conformalSymplecticNormal_add hD hn ((hf.contMDiff y).of_le (by simp))
    (hf.mfderiv_injective (by simp) y)
  rw [finrank_zero_of_subsingleton] at this
  omega

end Isotropic

/-! ### Local defining forms -/

section DefiningForm

variable (J f y) in
/-- The **symplectic form on the conformal symplectic normal space defined by a local defining
form.** If the one-form `α` has kernel `D_(f y)` at `f y`, then `α_(f y)` identifies the line
`T_(f y) M ⧸ D_(f y)` with `ℝ`, and turns the Levi form on the conformal symplectic normal space
of `f` at `y` into the symplectic form `[u], [v] ↦ α_(f y) (L_D (u, v))`. -/
def IsContactDistribution.normalSymplecticForm (hD : IsContactDistribution I n D)
    (α : RoughForm I M ℝ 1) (hα : α.ker (f y) = D (f y)) :
    SymplecticForm (ConformalSymplecticNormal J D f y) where
  toBilinForm := (conformalSymplecticNormalForm J D f y).compr₂
    ((D (f y)).liftQ (α.eval (f y)) ((α.ker_eq_ker_eval (f y)).symm.trans hα).ge)
  isAlt x := by simp [isAlt_conformalSymplecticNormalForm.self_eq_zero x]
  nondegenerate :=
    have : FiniteDimensional ℝ (TangentSpace I (f y)) := inferInstanceAs (FiniteDimensional ℝ E)
    isAlt_distributionLeviForm.isRefl.nondegenerate_compr₂_symplecticNormalForm
      (hD.bijective_distributionLeviForm (f y)).injective (hD.finrank_quotient (f y))
      (LinearMap.ker_eq_bot.1
        (Submodule.ker_liftQ_eq_bot _ _ _ ((α.ker_eq_ker_eval (f y)).symm.trans hα).le))

/-- **The symplectic form of a defining form evaluates the Levi form.** If `w` represents
`L_D (u, v)` in the line `T_(f y) M ⧸ D_(f y)`, then the symplectic form of `α` sends
`([u], [v])` to `α_(f y) (w)`. -/
theorem IsContactDistribution.normalSymplecticForm_mk (hD : IsContactDistribution I n D)
    {α : RoughForm I M ℝ 1} (hα : α.ker (f y) = D (f y))
    {u v : ((LinearMap.range (mfderiv J I f y).toLinearMap).comap (D (f y)).subtype).orthogonalBilin
      (distributionLeviForm D (f y))} {w : TangentSpace I (f y)}
    (hw : (D (f y)).mkQ w = distributionLeviForm D (f y) u v) :
    hD.normalSymplecticForm J f y α hα (Submodule.Quotient.mk u) (Submodule.Quotient.mk v) =
      α (f y) ![w] := by
  simp only [normalSymplecticForm, LinearMap.compr₂_apply, conformalSymplecticNormalForm_mk]
  rw [← hw, Submodule.mkQ_apply, Submodule.liftQ_apply, RoughForm.eval_apply]

/-- **The symplectic form of a local defining form is `dα`.** Let `D` be a `C^n` contact
structure, with `1 ≤ n`, and let the one-form `α` be differentiable at `f y` with kernel `D` on a
neighbourhood of `f y`. Then the symplectic form of `α` on the conformal symplectic normal space
of `f` at `y` is `[u], [v] ↦ dα_(f y) (u, v)`. -/
theorem IsContactDistribution.normalSymplecticForm_mk_eq_mextDeriv
    (hD : IsContactDistribution I n D) (hn : 1 ≤ n) {α : RoughForm I M ℝ 1}
    (hαd : MDifferentiableAt I (I.prod 𝓘(ℝ, E [⋀^Fin 1]→L[ℝ] ℝ))
      (fun z ↦ TotalSpace.mk' (E [⋀^Fin 1]→L[ℝ] ℝ) z (α z)) (f y))
    (hDα : ∀ᶠ z in 𝓝 (f y), α.ker z = D z)
    (u v : ((LinearMap.range (mfderiv J I f y).toLinearMap).comap (D (f y)).subtype).orthogonalBilin
      (distributionLeviForm D (f y))) :
    hD.normalSymplecticForm J f y α hDα.self_of_nhds (Submodule.Quotient.mk u)
        (Submodule.Quotient.mk v) =
      mextDeriv α (f y) ![(u : D (f y)), (v : D (f y))] := by
  obtain ⟨U, hU, hxU, X, hX⟩ := isContMDiffDistribution_iff.1 hD.isContMDiffDistribution (f y)
  obtain ⟨w, hw⟩ := (D (f y)).mkQ_surjective (distributionLeviForm D (f y) u v)
  rw [hD.normalSymplecticForm_mk hDα.self_of_nhds hw]
  exact RoughForm.apply_eq_mextDeriv_of_mkQ_eq_distributionLeviForm (hX.of_le hn)
    (hU.mem_nhds hxU) hαd (hDα.mono fun _ h ↦ h.ge) hw

/-- **Transition law.** Multiplying a defining form `α` by a function `g` not vanishing at `f y`
multiplies its symplectic form on the conformal symplectic normal space by `g (f y)`. -/
theorem IsContactDistribution.normalSymplecticForm_fun_smul (hD : IsContactDistribution I n D)
    {α : RoughForm I M ℝ 1} (hα : α.ker (f y) = D (f y)) {g : M → ℝ} (hg : g (f y) ≠ 0) :
    hD.normalSymplecticForm J f y (fun z ↦ g z • α z) (by rw [RoughForm.ker_fun_smul hg, hα]) =
      (hD.normalSymplecticForm J f y α hα).rescale (g (f y)) hg := by
  apply SymplecticForm.toBilinForm_injective
  refine LinearMap.ext fun a ↦ LinearMap.ext fun b ↦ ?_
  induction a using Submodule.Quotient.induction_on with
  | H u =>
    induction b using Submodule.Quotient.induction_on with
    | H v =>
      obtain ⟨w, hw⟩ := (D (f y)).mkQ_surjective (distributionLeviForm D (f y) u v)
      have h₁ := hD.normalSymplecticForm_mk (J := J) (by rw [RoughForm.ker_fun_smul hg, hα]) hw
      have h₂ := hD.normalSymplecticForm_mk (J := J) hα hw
      beta_reduce at h₁ h₂
      rw [SymplecticForm.rescale_toBilinForm, LinearMap.smul_apply, LinearMap.smul_apply, h₁, h₂,
        ContinuousAlternatingMap.smul_apply]

end DefiningForm

end TauCeti
