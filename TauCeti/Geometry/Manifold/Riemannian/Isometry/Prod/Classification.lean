/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Prod.Ricci
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Prod.Factorization
public import TauCeti.Geometry.Manifold.MFDeriv.Separation

/-!
# Isometry groups of products with distinct Ricci constants

An isometry of a product of connected Einstein manifolds preserves each factor if their
Ricci constants differ. The Ricci tensor identifies the two tangent summands; zero mixed
derivatives then make the coordinate maps independent of the other variable. Hence the full
isometry group is the product of the two factor isometry groups. The factors may have
boundary or corners.

This criterion applies to the product geometries `S² × ℝ` and `ℍ² × ℝ`, whose surface and
line factors have distinct Ricci constants.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, second edition, Chapter 7
  (Ricci curvature of products).
* P. Scott, *The geometries of 3-manifolds*, Bull. London Math. Soc. 15 (1983),
  Section 4 (the product geometries).
-/

public section

noncomputable section

open Bundle CovariantDerivative Manifold
open scoped Manifold ContDiff TauCeti

namespace TauCeti.RiemannianIsometry

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [PreconnectedSpace M] [Nonempty M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N] [T2Space N]
  [PreconnectedSpace N] [Nonempty N]
  [RiemannianBundle (fun y : N ↦ TangentSpace J y)]
  [IsContMDiffRiemannianBundle J ∞ F (fun y : N ↦ TangentSpace J y)]
  {a b : ℝ}

/-- Distinct constant Ricci eigenvalues force every product isometry to preserve the two
factors. The factor maps are Riemannian isometries, with no separation hypothesis on the
original map. -/
theorem prodCongrHom_surjective_of_ricciTensor_eq_smul_inner
    (hM : ∀ x u v, (leviCivitaConnection I M).ricciTensor x u v = a * inner ℝ u v)
    (hN : ∀ y u v, (leviCivitaConnection J N).ricciTensor y u v = b * inner ℝ u v)
    (hab : a ≠ b) : Function.Surjective (prodCongrHom I M J N) := by
  intro Q
  obtain ⟨x₀⟩ := ‹Nonempty M›
  obtain ⟨y₀⟩ := ‹Nonempty N›
  have hsep := (Q.mdifferentiable.eq_prodMap_iff_mfderiv_mixed_eq_zero x₀ y₀).mpr
    ⟨fun p v => (Q.fst_mfderiv_eq_zero_iff_of_ricciTensor_eq_smul_inner p
        (hM p.1) (hN p.2) (hM (Q p).1) (hN (Q p).2) hab (0, v)).mpr rfl,
      fun p v => (Q.snd_mfderiv_eq_zero_iff_of_ricciTensor_eq_smul_inner p
        (hM p.1) (hN p.2) (hM (Q p).1) (hN (Q p).2) hab (v, 0)).mpr rfl⟩
  obtain ⟨Φ, Ψ, h⟩ := Q.exists_prodCongr_of_eq_prodMap _ _ hsep
  exact ⟨(Φ, Ψ), by simpa only [prodCongrHom_apply] using h⟩

/-- The full isometry group of a product of connected Einstein manifolds with distinct
Ricci constants is the direct product of the factor isometry groups. -/
def prodIsomMulEquivOfRicciTensorEqSmulInner
    (hM : ∀ x u v, (leviCivitaConnection I M).ricciTensor x u v = a * inner ℝ u v)
    (hN : ∀ y u v, (leviCivitaConnection J N).ricciTensor y u v = b * inner ℝ u v)
    (hab : a ≠ b) :
    (Isom I M × Isom J N) ≃* Isom (I.prod J) (M × N) :=
  MulEquiv.ofBijective (prodCongrHom I M J N)
    ⟨prodCongrHom_injective, prodCongrHom_surjective_of_ricciTensor_eq_smul_inner hM hN hab⟩

/-- The equivalence sends a pair of factor isometries to their product. -/
@[simp]
theorem prodIsomMulEquivOfRicciTensorEqSmulInner_apply
    (hM : ∀ x u v, (leviCivitaConnection I M).ricciTensor x u v = a * inner ℝ u v)
    (hN : ∀ y u v, (leviCivitaConnection J N).ricciTensor y u v = b * inner ℝ u v)
    (hab : a ≠ b) (Φ : Isom I M × Isom J N) :
    prodIsomMulEquivOfRicciTensorEqSmulInner hM hN hab Φ = Φ.1.prodCongr Φ.2 :=
  prodCongrHom_apply Φ

/-- The inverse equivalence recovers the two factor isometries, whose product agrees
with the given isometry at every point. -/
@[simp]
theorem prodIsomMulEquivOfRicciTensorEqSmulInner_symm_apply
    (hM : ∀ x u v, (leviCivitaConnection I M).ricciTensor x u v = a * inner ℝ u v)
    (hN : ∀ y u v, (leviCivitaConnection J N).ricciTensor y u v = b * inner ℝ u v)
    (hab : a ≠ b) (Q : Isom (I.prod J) (M × N)) (p : M × N) :
    (fun g : Isom I M × Isom J N => (g.1 p.1, g.2 p.2))
      ((prodIsomMulEquivOfRicciTensorEqSmulInner hM hN hab).symm Q) = Q p := by
  have h := congrArg (fun Φ : Isom (I.prod J) (M × N) => Φ p)
    ((prodIsomMulEquivOfRicciTensorEqSmulInner hM hN hab).apply_symm_apply Q)
  simpa only [prodIsomMulEquivOfRicciTensorEqSmulInner_apply, prodCongr_apply] using h

end TauCeti.RiemannianIsometry

end
