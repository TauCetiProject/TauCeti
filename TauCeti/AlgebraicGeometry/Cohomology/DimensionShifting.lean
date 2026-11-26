/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Cohomology.Biproduct
public import TauCeti.AlgebraicGeometry.Cohomology.LongExactSequence
public import TauCeti.AlgebraicGeometry.Modules.FinitePresentation.Abelian
public import TauCeti.AlgebraicGeometry.Modules.Tensor.Product
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.Free.Basic

/-!
# Finiteness of cohomology by dimension shifting

Let `X` be a locally Noetherian scheme over a Noetherian ring `R`. This file proves that the
cohomology modules `Hᵠ(X, F)` of every quasi-coherent sheaf `F` of finite type are finitely
generated over `R` as soon as

* cohomology of such sheaves vanishes above some fixed degree `N`, and
* every such `F` is a quotient of a quasi-coherent sheaf `E` of finite type whose cohomology is
  finitely generated in every degree.

The argument is descending induction on `q` (Hartshorne, proof of Theorem III.5.2). The kernel `K`
of an epimorphism `E ⟶ F` is again quasi-coherent of finite type because `X` is locally
Noetherian (`Scheme.Modules.isFinitePresentation_kernel`), and the long exact cohomology sequence
`Hᵠ(X, E) ⟶ Hᵠ(X, F) ⟶ Hᵠ⁺¹(X, K)` exhibits `Hᵠ(X, F)` between a finitely generated module and a
submodule of a finitely generated module over a Noetherian ring
(`Scheme.Modules.finite_cohomology_X₃`). On projective space over `R`, the
sources `E` are the finite sums `𝒪(-n)^{⊕I} = 𝒪^{⊕I} ⊗ 𝒪(-n)` provided by Serre's theorem; their
cohomology is computed here from that of the summand.

## Main results

* `Scheme.Modules.finite_cohomology_free_tensor`: `Hᵠ(X, 𝒪^{⊕I} ⊗ L)` is finitely generated when
  `I` is finite and `Hᵠ(X, L)` is finitely generated.
* `Scheme.Modules.finite_cohomology_of_forall_exists_epi`: the dimension-shifting criterion above.

## References

* R. Hartshorne, *Algebraic Geometry*, GTM 52, Springer, 1977, Theorem III.5.2 and its proof.
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules

universe u

variable (R : Type u) [CommRing R] {X : Scheme.{u}} [X.Over (Spec (.of R))]

/-- The cohomology of `𝒪^{⊕I} ⊗ L`, for a finite type `I`, is finitely generated over the base
ring in every degree in which the cohomology of `L` is: `𝒪^{⊕I} ⊗ L` is the direct sum of `I`
copies of `L`. -/
instance finite_cohomology_free_tensor (I : Type u) [Finite I] (L : X.Modules) (q : ℕ)
    [Module.Finite R (Cohomology L q)] :
    Module.Finite R (Cohomology ((SheafOfModules.free I : X.Modules) ⊗ L) q) := by
  have : Fintype I := .ofFinite I
  -- Tensoring is additive in each variable, so it commutes with the finite direct sum
  -- `𝒪^{⊕I} ≅ ⨁_I 𝒪`.
  -- The instances are stated on `X.Modules`: the tensor product and `biproductIsoFree` are
  -- elaborated in the defeq category `SheafOfModules (ringCatSheaf X.sheaf)`, where instance
  -- search does not find them for `X.Modules`.
  have : MonoidalPreadditive X.Modules := TauCeti.SheafOfModules.monoidalPreadditive X.sheaf
  have : HasBiproduct (C := X.Modules) fun _ : I ↦ L := HasBiproduct.of_hasCoproduct _
  have : HasBiproduct (C := X.Modules) fun _ : I ↦ 𝟙_ X.Modules := HasBiproduct.of_hasCoproduct _
  let e₀ : Iso (C := X.Modules) (SheafOfModules.free I) (⨁ fun _ : I ↦ 𝟙_ X.Modules) :=
    (TauCeti.SheafOfModules.biproductIsoFree (R := X.sheaf) I).symm
  let e : Iso (C := X.Modules) ((SheafOfModules.free I : X.Modules) ⊗ L) (⨁ fun _ : I ↦ L) :=
    whiskerRightIso e₀ L ≪≫ (tensorRight L).mapBiproduct _ ≪≫ biproduct.mapIso fun _ ↦ λ_ L
  exact .equiv ((cohomologyBiproductLinearEquiv R (fun _ : I ↦ L) q).symm ≪≫ₗ
    (cohomologyBaseLinearEquivOfIso R e q).symm)

/-- **Finiteness of cohomology by dimension shifting.** Let `X` be a locally Noetherian scheme over
a Noetherian ring `R`. Suppose that quasi-coherent sheaves of finite type on `X` have no cohomology
in degrees at least `N`, and that each of them is a quotient of a quasi-coherent sheaf of finite
type whose cohomology is finitely generated over `R` in every degree. Then every quasi-coherent
sheaf of finite type on `X` has finitely generated cohomology over `R` in every degree. -/
theorem finite_cohomology_of_forall_exists_epi [IsLocallyNoetherian X] [IsNoetherianRing R]
    (N : ℕ)
    (hvan : ∀ (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] (q : ℕ), N ≤ q →
      Subsingleton (Cohomology F q))
    (hepi : ∀ (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType],
      ∃ (E : X.Modules) (π : E ⟶ F), Epi π ∧ E.IsQuasicoherent ∧ E.IsFiniteType ∧
        ∀ q, Module.Finite R (Cohomology E q))
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] (q : ℕ) :
    Module.Finite R (Cohomology F q) := by
  -- Descending induction on the degree, starting from the vanishing range `N ≤ q`.
  suffices h : ∀ k q, N ≤ q + k → ∀ (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType],
      Module.Finite R (Cohomology F q) from h N q (by omega) F
  intro k
  induction k with
  | zero =>
    intro q hq F _ _
    have := hvan F q (by omega)
    infer_instance
  | succ k ih =>
    intro q hq F _ _
    obtain ⟨E, π, _, _, _, hE⟩ := hepi F
    -- The kernel of `π` is quasi-coherent of finite type, so the induction hypothesis applies to
    -- it in degree `q + 1`.
    let S := ShortComplex.mk (kernel.ι π) π (kernel.condition π)
    have hS : S.ShortExact :=
      .mk' (ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel π)) inferInstance ‹_›
    have : Module.Finite R (Cohomology S.X₂ q) := hE q
    have : Module.Finite R (Cohomology S.X₁ (q + 1)) := ih (q + 1) (by omega) (kernel π)
    exact finite_cohomology_X₃ R X hS q (q + 1) rfl

end AlgebraicGeometry.Scheme.Modules
