/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Affinoid.Subdomain.Laurent
import TauCeti.RingTheory.Affinoid.QuotientNorm
import TauCeti.RingTheory.Huber.ClosedSubmodule
import TauCeti.RingTheory.Huber.Normed

/-!
# Iterated Laurent presentations

Let `φ : A → B` represent the Laurent domain `L(f, g⁻¹)`. Imposing a second family of Laurent
inequalities on `B`, pulled back from `A`, gives the combined presentation
`A⟨f, f', g⁻¹, (g')⁻¹⟩`. The comparison respects restriction from `B`, not just coefficients
from `A`. This identifies the coordinate algebras used for intersections of Laurent domains.

The first representing algebra may carry any complete ultrametric algebra norm: it need not
use a particular quotient norm. The final quotient topologies agree under the comparison;
no equality of quotient norms is asserted. Empty families and the zero algebra are allowed,
and nilpotents are retained throughout.

## References

* Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*, §§6.1.4 and 7.2.2.
-/

public section

namespace TauCeti

universe u

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

section Points

variable {A B : Type u} [CommRing A] [Algebra K A] [CommRing B] [Algebra K B]
  {r s r' s' : ℕ} {f : Fin r → A} {g : Fin s → A}
  {φ : A →ₐ[K] B}

namespace IsAffinoidSubdomainMap

/-- The image of the Laurent domain defined by a second family is the Laurent domain defined
by concatenating both families. This is a statement on classical points, with the first
Laurent domain represented by `φ`. -/
theorem image_laurentDomain (hφ : IsAffinoidSubdomainMap φ (laurentDomain K f g))
    (hA : IsAffinoidAlgebra K A) (f' : Fin r' → A) (g' : Fin s' → A) :
    hφ.isAffinoidAlgebra.maximalSpectrumComap φ ''
      laurentDomain K (φ ∘ f') (φ ∘ g') =
        laurentDomain K (Fin.append f f') (Fin.append g g') := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hx := hφ.range_maximalSpectrumComap_subset ⟨y, rfl⟩
    simp only [mem_laurentDomain] at hx hy ⊢
    simp only [IsAffinoidAlgebra.pointNorm_maximalSpectrumComap] at hx ⊢
    exact ⟨Fin.addCases (by simpa using hx.1) (by simpa using hy.1),
      Fin.addCases (by simpa using hx.2) (by simpa using hy.2)⟩
  · intro hx
    rw [mem_laurentDomain] at hx
    have hx₁ : x ∈ laurentDomain K f g :=
      mem_laurentDomain.mpr ⟨fun i ↦ by simpa using hx.1 (Fin.castAdd r' i),
        fun j ↦ by simpa using hx.2 (Fin.castAdd s' j)⟩
    obtain ⟨y, rfl⟩ := (hφ.range_maximalSpectrumComap hA).symm ▸ hx₁
    refine ⟨y, ?_, rfl⟩
    simp only [mem_laurentDomain, Function.comp_apply]
    exact ⟨fun i ↦ by
      simpa only [IsAffinoidAlgebra.pointNorm_maximalSpectrumComap, Fin.append_right]
        using hx.1 (Fin.natAdd r i), fun j ↦ by
      simpa only [IsAffinoidAlgebra.pointNorm_maximalSpectrumComap, Fin.append_right]
        using hx.2 (Fin.natAdd s j)⟩

end IsAffinoidSubdomainMap

end Points

namespace LaurentFraction

section Subdomain

variable {A B : Type u} [CommRing A] [Algebra K A]
  [NormedCommRing B] [NormedAlgebra K B] [IsUltrametricDist B] [CompleteSpace B]
  {r s r' s' : ℕ} {f : Fin r → A} {g : Fin s → A} {φ : A →ₐ[K] B}

/-- Successively imposing Laurent inequalities represents the concatenated Laurent domain,
compatibly with the composite structure map from `A`. -/
theorem isAffinoidSubdomainMap_iterate
    (hφ : IsAffinoidSubdomainMap φ (laurentDomain K f g)) (hA : IsAffinoidAlgebra K A)
    (f' : Fin r' → A) (g' : Fin s' → A) :
    IsAffinoidSubdomainMap
      ((IsScalarTower.toAlgHom K B (LaurentFraction (φ ∘ f') (φ ∘ g'))).comp φ)
      (laurentDomain K (Fin.append f f') (Fin.append g g')) := by
  rw [← hφ.image_laurentDomain hA f' g']
  exact hφ.comp hA (isAffinoidSubdomainMap hφ.isAffinoidAlgebra)

end Subdomain

section Restriction

variable {A B : Type u}
  [NormedCommRing A] [NormedAlgebra K A] [IsUltrametricDist A] [CompleteSpace A]
  [CommRing B] [Algebra K B]
  {r s r' s' : ℕ} {f : Fin r → A} {g : Fin s → A} {φ : A →ₐ[K] B}
  (hφ : IsAffinoidSubdomainMap φ (laurentDomain K f g)) (hA : IsAffinoidAlgebra K A)
  (f' : Fin r' → A) (g' : Fin s' → A)

private theorem range_append_subset :
    Set.range ((isAffinoidAlgebra hA (Fin.append f f') (Fin.append g g')).maximalSpectrumComap
      (IsScalarTower.toAlgHom K A _)) ⊆ laurentDomain K f g := by
  intro x hx
  have hx := (isAffinoidSubdomainMap hA (f := Fin.append f f')
    (g := Fin.append g g')).range_maximalSpectrumComap_subset hx
  rw [mem_laurentDomain] at hx ⊢
  exact ⟨fun i ↦ by simpa using hx.1 (Fin.castAdd r' i),
    fun j ↦ by simpa using hx.2 (Fin.castAdd s' j)⟩

/-- Restriction from the first representing algebra to the combined Laurent presentation. It
is the unique map extending the structure map from `A`. No norm on the first algebra is needed. -/
noncomputable def appendLeft :
    B →ₐ[K] LaurentFraction (Fin.append f f') (Fin.append g g') :=
  hφ.lift (isAffinoidAlgebra hA _ _) (IsScalarTower.toAlgHom K A _)
    (range_append_subset hA f' g')

/-- Restriction to the combined presentation preserves coefficients. -/
@[simp]
theorem appendLeft_apply (a : A) :
    appendLeft hφ hA f' g' (φ a) =
      algebraMap A (LaurentFraction (Fin.append f f') (Fin.append g g')) a :=
  hφ.lift_apply ..

end Restriction

variable {A B : Type u}
  [NormedCommRing A] [NormedAlgebra K A] [IsUltrametricDist A] [CompleteSpace A]
  [NormedCommRing B] [NormedAlgebra K B] [IsUltrametricDist B] [CompleteSpace B]
  {r s r' s' : ℕ} {f : Fin r → A} {g : Fin s → A} {φ : A →ₐ[K] B}
  (hφ : IsAffinoidSubdomainMap φ (laurentDomain K f g)) (hA : IsAffinoidAlgebra K A)
  (f' : Fin r' → A) (g' : Fin s' → A)

local notation "C" => LaurentFraction (φ ∘ f') (φ ∘ g')
local notation "D" => LaurentFraction (Fin.append f f') (Fin.append g g')

/-- **The iterated Laurent presentation.** For any completely normed algebra representing the
first Laurent domain, the second Laurent fraction algebra is isomorphic to the combined
presentation as a topological `K`-algebra. No equality of quotient norms is asserted. -/
noncomputable def iterateEquiv : C ≃A[K] D := by
  let hC := isAffinoidAlgebra hφ.isAffinoidAlgebra (φ ∘ f') (φ ∘ g')
  let hD := isAffinoidAlgebra hA (Fin.append f f') (Fin.append g g')
  -- The quotient Gauss norms give the already specified quotient topologies.
  haveI := (hA.isRestricted_subring (τ := Fin ((r + r') + (s + s')))).isNoetherianRing
  haveI := (hφ.isAffinoidAlgebra.isRestricted_subring (τ := Fin (r' + s'))).isNoetherianRing
  haveI := Huber.IsTateRing.of_normedAlgebra K
    (MvPowerSeries.IsRestricted.subring (R := A) (fun _ : Fin ((r + r') + (s + s')) ↦ 1))
  haveI := Huber.IsTateRing.of_normedAlgebra K
    (MvPowerSeries.IsRestricted.subring (R := B) (fun _ : Fin (r' + s') ↦ 1))
  haveI : IsClosed (laurentFractionIdeal (Fin.append f f') (Fin.append g g') : Set
      (MvPowerSeries.IsRestricted.subring (R := A)
        (fun _ : Fin ((r + r') + (s + s')) ↦ 1))) := Huber.isClosed_of_isNoetherian _
  haveI : IsClosed (laurentFractionIdeal (φ ∘ f') (φ ∘ g') : Set
      (MvPowerSeries.IsRestricted.subring (R := B) (fun _ : Fin (r' + s') ↦ 1))) :=
    Huber.isClosed_of_isNoetherian _
  haveI := hC.isNoetherianRing
  exact IsAffinoidAlgebra.toContinuousAlgEquiv (K := K) (A := C) (B := D) hD
    ((isAffinoidSubdomainMap_iterate hφ hA f' g').algEquiv (isAffinoidSubdomainMap hA))

private theorem iterateEquiv_coefficient (a : A) :
    iterateEquiv hφ hA f' g' (algebraMap B C (φ a)) = algebraMap A D a := by
  simp only [iterateEquiv, IsAffinoidAlgebra.coe_toContinuousAlgEquiv]
  exact IsAffinoidSubdomainMap.algEquiv_apply ..

/-- The inverse iteration comparison preserves the coefficient map. -/
@[simp]
theorem iterateEquiv_symm_algebraMap (a : A) :
    (iterateEquiv hφ hA f' g').symm (algebraMap A D a) = algebraMap B C (φ a) := by
  rw [← iterateEquiv_coefficient hφ hA f' g' a, ContinuousAlgEquiv.symm_apply_apply]

/-- The iteration comparison intertwines restriction from the first Laurent algebra with
restriction to the combined presentation. -/
@[simp]
theorem iterateEquiv_algebraMap (b : B) :
    iterateEquiv hφ hA f' g' (algebraMap B C b) = appendLeft hφ hA f' g' b := by
  have he : (iterateEquiv hφ hA f' g').toAlgHom.comp (IsScalarTower.toAlgHom K B C) =
      appendLeft hφ hA f' g' := by
    apply hφ.algHom_ext (isAffinoidAlgebra hA _ _)
    ext a
    simp [iterateEquiv_coefficient]
  exact AlgHom.congr_fun he b

/-- In the inverse direction, restriction from the first Laurent algebra is the second
Laurent structure map. -/
@[simp]
theorem iterateEquiv_symm_appendLeft (b : B) :
    (iterateEquiv hφ hA f' g').symm (appendLeft hφ hA f' g' b) = algebraMap B C b := by
  rw [← iterateEquiv_algebraMap, ContinuousAlgEquiv.symm_apply_apply]

end LaurentFraction

end TauCeti
