/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Diffeomorph
public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
public import TauCeti.Geometry.Manifold.VectorBundle.Tangent.Basic
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# Diffeomorphisms of products

If a diffeomorphism between nonempty products has underlying map `Prod.map f g`, then
both `f` and `g` are diffeomorphisms. No smoothness of the factor maps or their inverses
is assumed: each is recovered as a slice of the product diffeomorphism or its inverse.
This lets one promote separation of a smooth map into separation by bundled equivalences.

`Diffeomorph.prodAssocOfModels` reassociates three manifold factors with independent model
vector spaces, generalizing Mathlib's `Diffeomorph.prodAssoc`, where the last two coincide.

The four-way exchange `((a, b), (c, d)) ↦ ((a, c), (b, d))` of a product of two products is
the diffeomorphism `Diffeomorph.prodProdProdComm`, the smooth counterpart of
`Equiv.prodProdProdComm`. It regroups a product of relations `M₁ ⇝ N₁` and `M₂ ⇝ N₂` as a
relation `M₁ × M₂ ⇝ N₁ × N₂`.

For a diffeomorphism `ψ : M ≃ V` onto a normed space and a `C^n` map `f : M → W` into a normed
space, the shear `(x, y) ↦ (ψ x, y + f x)` is the diffeomorphism `Diffeomorph.prodShear` of
`M × W` onto `V × W`, the smooth counterpart of `Equiv.prodShear` for the translations
`y ↦ y + f x`. Its differential sends `(u, r)` to `(dψ u, r + df u)`
(`Diffeomorph.mfderiv_prodShear_apply`).
-/

public section

open scoped Manifold ContDiff

namespace Diffeomorph

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners 𝕜 F G}
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
  {F' : Type*} [NormedAddCommGroup F'] [NormedSpace 𝕜 F']
  {G' : Type*} [TopologicalSpace G'] {J' : ModelWithCorners 𝕜 F' G'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
  {N' : Type*} [TopologicalSpace N'] [ChartedSpace G' N']
  {n : ℕ∞ω}

/-- The factors of a diffeomorphism whose underlying map separates are themselves
`C^n` diffeomorphisms. Nonemptiness excludes an empty product hiding an arbitrary factor. -/
theorem exists_factors_of_eq_prodMap
    (Q : (M × N) ≃ₘ^n⟮I.prod J, I'.prod J'⟯ (M' × N'))
    [Nonempty M] [Nonempty N] (f : M → M') (g : N → N')
    (hQ : ⇑Q = Prod.map f g) :
    ∃ (φ : M ≃ₘ^n⟮I, I'⟯ M') (ψ : N ≃ₘ^n⟮J, J'⟯ N'), ⇑φ = f ∧ ⇑ψ = g := by
  obtain ⟨x₀⟩ := ‹Nonempty M›
  obtain ⟨y₀⟩ := ‹Nonempty N›
  have hQ' (p : M × N) : Q p = (f p.1, g p.2) := by rw [hQ, Prod.map_apply']
  -- The inverse factors are the slices of `Q.symm` through `(·, g y₀)` and `(f x₀, ·)`.
  refine ⟨⟨⟨f, fun u ↦ (Q.symm (u, g y₀)).1, fun x ↦ ?_, fun u ↦ ?_⟩, ?_,
      (Q.symm.contMDiff.comp (contMDiff_id.prodMk contMDiff_const)).fst⟩,
    ⟨⟨g, fun v ↦ (Q.symm (f x₀, v)).2, fun y ↦ ?_, fun v ↦ ?_⟩, ?_,
      (Q.symm.contMDiff.comp (contMDiff_const.prodMk contMDiff_id)).snd⟩, rfl, rfl⟩
  · simpa [hQ'] using congrArg Prod.fst (Q.symm_apply_apply (x, y₀))
  · simpa [hQ'] using congrArg Prod.fst (Q.apply_symm_apply (u, g y₀))
  · simpa [hQ'] using
      (Q.contMDiff.comp (contMDiff_id.prodMk (contMDiff_const (c := y₀)))).fst
  · simpa [hQ'] using congrArg Prod.snd (Q.symm_apply_apply (x₀, y))
  · simpa [hQ'] using congrArg Prod.snd (Q.apply_symm_apply (f x₀, v))
  · simpa [hQ'] using
      (Q.contMDiff.comp ((contMDiff_const (c := x₀)).prodMk contMDiff_id)).snd

section prodAssocOfModels

variable (I J I' M N M' n)

/-- Reassociation of three manifold factors with independent model vector spaces. -/
def prodAssocOfModels :
    ((M × N) × M') ≃ₘ^n⟮(I.prod J).prod I', I.prod (J.prod I')⟯ M × (N × M') where
  toEquiv := Equiv.prodAssoc M N M'
  contMDiff_toFun := contMDiff_prod_assoc
  contMDiff_invFun := (contMDiff_fst.prodMk contMDiff_snd.fst).prodMk contMDiff_snd.snd

/-- Reassociation sends `((x, y), z)` to `(x, (y, z))`. -/
@[simp]
theorem prodAssocOfModels_apply (p : (M × N) × M') :
    prodAssocOfModels I J I' M N M' n p = (p.1.1, (p.1.2, p.2)) := (rfl)

/-- Inverse reassociation sends `(x, (y, z))` to `((x, y), z)`. -/
@[simp]
theorem prodAssocOfModels_symm_apply (p : M × (N × M')) :
    (prodAssocOfModels I J I' M N M' n).symm p = ((p.1, p.2.1), p.2.2) := (rfl)

end prodAssocOfModels

section prodProdProdComm

variable (I J I' J' M N M' N' n)

/-- `(M × N) × (M' × N')` is diffeomorphic to `(M × M') × (N × N')`, by exchanging the two
middle factors. -/
def prodProdProdComm :
    ((M × N) × (M' × N')) ≃ₘ^n⟮(I.prod J).prod (I'.prod J'), (I.prod I').prod (J.prod J')⟯
      ((M × M') × (N × N')) where
  contMDiff_toFun := (contMDiff_fst.fst.prodMk contMDiff_snd.fst).prodMk
    (contMDiff_fst.snd.prodMk contMDiff_snd.snd)
  contMDiff_invFun := (contMDiff_fst.fst.prodMk contMDiff_snd.fst).prodMk
    (contMDiff_fst.snd.prodMk contMDiff_snd.snd)
  toEquiv := Equiv.prodProdProdComm M N M' N'

/-- The inverse of the four-way exchange is the four-way exchange of the regrouped factors. -/
@[simp]
theorem prodProdProdComm_symm :
    (prodProdProdComm I J I' J' M N M' N' n).symm = prodProdProdComm I I' J J' M M' N N' n :=
  (rfl)

/-- The underlying map of the four-way exchange is `Equiv.prodProdProdComm`. -/
@[simp]
theorem coe_prodProdProdComm :
    ⇑(prodProdProdComm I J I' J' M N M' N' n) = Equiv.prodProdProdComm M N M' N' :=
  (rfl)

end prodProdProdComm

section prodShear

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace 𝕜 W]

/-- The **shear** `(x, y) ↦ (ψ x, y + f x)` of `M × W` along a diffeomorphism `ψ : M ≃ V` onto a
normed space and a `C^n` map `f : M → W`, as a diffeomorphism onto `V × W`. -/
def prodShear (ψ : M ≃ₘ^n⟮I, 𝓘(𝕜, V)⟯ V) {f : M → W} (hf : ContMDiff I 𝓘(𝕜, W) n f) :
    (M × W) ≃ₘ^n⟮I.prod 𝓘(𝕜, W), 𝓘(𝕜, V × W)⟯ (V × W) where
  toFun p := (ψ p.1, p.2 + f p.1)
  invFun q := (ψ.symm q.1, q.2 - f (ψ.symm q.1))
  left_inv p := by simp
  right_inv q := by simp
  contMDiff_toFun :=
    (ψ.contMDiff.comp contMDiff_fst).prodMk_space (contMDiff_snd.add (hf.comp contMDiff_fst))
  contMDiff_invFun := by
    have h : ContMDiff 𝓘(𝕜, V × W) I n fun q : V × W ↦ ψ.symm q.1 :=
      ψ.symm.contMDiff.comp contDiff_fst.contMDiff
    exact h.prodMk (contDiff_snd.contMDiff.sub (hf.comp h))

variable (ψ : M ≃ₘ^n⟮I, 𝓘(𝕜, V)⟯ V) {f : M → W} (hf : ContMDiff I 𝓘(𝕜, W) n f)

/-- The shear `ψ.prodShear hf` sends `(x, y)` to `(ψ x, y + f x)`. -/
@[simp]
theorem prodShear_apply (p : M × W) : ψ.prodShear hf p = (ψ p.1, p.2 + f p.1) := (rfl)

/-- The inverse of the shear `ψ.prodShear hf` sends `(z, y)` to `(ψ⁻¹ z, y - f (ψ⁻¹ z))`. -/
@[simp]
theorem prodShear_symm_apply (q : V × W) :
    (ψ.prodShear hf).symm q = (ψ.symm q.1, q.2 - f (ψ.symm q.1)) := (rfl)

/-- The differential of the shear `ψ.prodShear hf` sends `(u, r)` to `(dψ u, r + df u)`. -/
theorem mfderiv_prodShear_apply (hn : n ≠ 0) (p : M × W)
    (w : TangentSpace (I.prod 𝓘(𝕜, W)) p) :
    mfderiv (I.prod 𝓘(𝕜, W)) 𝓘(𝕜, V × W) (ψ.prodShear hf) p w =
      (mvfderiv I ψ p.1 (TauCeti.Manifold.tangentSpaceProdEquiv p w).1,
        NormedSpace.fromTangentSpace p.2 (TauCeti.Manifold.tangentSpaceProdEquiv p w).2 +
          mvfderiv I f p.1 (TauCeti.Manifold.tangentSpaceProdEquiv p w).1) := by
  set fst := ContinuousLinearMap.fst 𝕜 E W
  -- The tangent spaces `TangentSpace I p.1`, `TangentSpace 𝓘(𝕜, V) (ψ p.1)` and
  -- `TangentSpace 𝓘(𝕜, W) (f p.1)` are by definition the model spaces `E`, `V` and `W`, so the
  -- differentials of `ψ` and `f` are linear maps between the model spaces.
  set dψ : E →L[𝕜] V := by exact mfderiv I 𝓘(𝕜, V) ψ p.1
  set df : E →L[𝕜] W := by exact mfderiv I 𝓘(𝕜, W) f p.1
  have hψ : HasMFDerivAt (I.prod 𝓘(𝕜, W)) 𝓘(𝕜, V) (fun p : M × W ↦ ψ p.1) p (dψ.comp fst) :=
    (ψ.mdifferentiable hn p.1).hasMFDerivAt.comp p (hasMFDerivAt_fst p)
  have hs : HasMFDerivAt (I.prod 𝓘(𝕜, W)) 𝓘(𝕜, W) (fun p : M × W ↦ p.2 + f p.1) p
      (ContinuousLinearMap.snd 𝕜 E W + df.comp fst) :=
    (hasMFDerivAt_snd p).add
      ((hf.mdifferentiable hn p.1).hasMFDerivAt.comp p (hasMFDerivAt_fst p))
  have h : HasMFDerivAt (I.prod 𝓘(𝕜, W)) 𝓘(𝕜, V × W) (ψ.prodShear hf) p
      ((dψ.comp fst).prod (ContinuousLinearMap.snd 𝕜 E W + df.comp fst)) :=
    ⟨(ψ.prodShear hf).continuous.continuousAt, hψ.2.prodMk hs.2⟩
  rw [h.mfderiv]
  simp only [TauCeti.Manifold.tangentSpaceProdEquiv_apply, NormedSpace.fromTangentSpace_apply]
  -- `mvfderiv` is `mfderiv` read through the identity identification of the tangent space of a
  -- normed space with the space itself, and the tangent space of `M × W` is `E × W`.
  rfl

end prodShear

end Diffeomorph
