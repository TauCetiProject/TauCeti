/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import TauCeti.AlgebraicGeometry.LineBundle.NonvanishingLocus
public import TauCeti.AlgebraicGeometry.LineBundle.TwistedSections
public import TauCeti.AlgebraicGeometry.Morphisms.FiniteType.Basic

/-!
# Finite affine generators extended as sections of a tensor power

Finite generators of affine nonvanishing charts become global sections after multiplying by
a common positive tensor power of the defining section. These sections provide the extra
coordinates used to construct a projective immersion.

## References

* R. Hartshorne, *Algebraic Geometry*, Chapter II, Proposition 5.14 and the proof of
  Proposition 7.6.
-/

public section

open CategoryTheory MonoidalCategory AlgebraicGeometry Opposite TopologicalSpace Filter TauCeti

noncomputable section

universe u

namespace TauCeti.AlgebraicGeometry.InvertibleSheaf

variable {X : Scheme.{u}} (L : InvertibleSheaf X)

/-- A family of global sections extending local generators in the specified tensor degree. -/
def IsTensorPowExtension {I : Type u} (s : I → Γ(L.obj, ⊤))
    {K : I → Type u} (f : ∀ i, K i → Γ(X, L.obj.nonvanishingLocus (s i)))
    (N : ℕ) (t : ∀ i, K i → Γ(TauCeti.tensorPow L.obj N, ⊤)) : Prop :=
  ∀ i k, (TauCeti.tensorPow L.obj N).presheaf.map
      (homOfLE (show L.obj.nonvanishingLocus (s i) ≤ ⊤ from le_top)).op (t i k) =
    f i k • Scheme.Modules.tensorPowSection
      (L.obj.presheaf.map
        (homOfLE (show L.obj.nonvanishingLocus (s i) ≤ ⊤ from le_top)).op (s i)) N

/-- The restriction equation supplied by an extension family. -/
theorem IsTensorPowExtension.map_eq {I : Type u} {s : I → Γ(L.obj, ⊤)}
    {K : I → Type u} {f : ∀ i, K i → Γ(X, L.obj.nonvanishingLocus (s i))}
    {N : ℕ} {t : ∀ i, K i → Γ(TauCeti.tensorPow L.obj N, ⊤)}
    (h : L.IsTensorPowExtension s f N t) (i : I) (k : K i) :
    (TauCeti.tensorPow L.obj N).presheaf.map
        (homOfLE (show L.obj.nonvanishingLocus (s i) ≤ ⊤ from le_top)).op (t i k) =
      f i k • Scheme.Modules.tensorPowSection
        (L.obj.presheaf.map
          (homOfLE (show L.obj.nonvanishingLocus (s i) ≤ ⊤ from le_top)).op (s i)) N :=
  h i k

/-- Finitely many local functions on finitely many nonvanishing loci extend simultaneously
as multiples of the corresponding powers of the defining sections, in one positive degree. -/
theorem exists_common_tensorPow_extensions [CompactSpace X] [QuasiSeparatedSpace X]
    {I : Type u} [Finite I] (s : I → Γ(L.obj, ⊤))
    {K : I → Type u} [∀ i, Finite (K i)]
    (f : ∀ i, K i → Γ(X, L.obj.nonvanishingLocus (s i))) :
    ∃ N : ℕ, 0 < N ∧ ∃ t : ∀ i, K i → Γ(TauCeti.tensorPow L.obj N, ⊤),
      IsTensorPowExtension L s f N t := by
  have hext := Filter.eventually_all.mpr fun p : Σ i, K i ↦
    Scheme.Modules.eventually_exists_map_eq_smul_tensorPowSection
      (by simpa using isCompact_univ) (by simpa using isQuasiSeparated_univ)
      (s p.fst) (f p.fst p.snd)
  obtain ⟨N, hN, hn⟩ := (Filter.eventually_gt_atTop 0 |>.and hext).exists
  choose t ht using hn
  exact ⟨N, hN, fun i k ↦ t ⟨i, k⟩, by
    intro i k
    exact ht ⟨i, k⟩⟩

/-- A finite affine nonvanishing cover admits finite local algebra generators and one positive
tensor degree in which all those generators extend as sections of the powered line bundle. -/
theorem exists_affine_generators_common_tensorPow {I : Type u} [Finite I]
    (s : I → Γ(L.obj, ⊤)) {R : Type u} [CommRing R] (c : R →+* Γ(X, ⊤))
    [LocallyOfFiniteType (X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom c))]
    (hs : ∀ i, IsAffineOpen (L.obj.nonvanishingLocus (s i)))
    (hcover : ⨆ i, L.obj.nonvanishingLocus (s i) = ⊤) :
    ∃ (K : I → Type u) (_ : ∀ i, Finite (K i))
      (f : ∀ i, K i → Γ(X, L.obj.nonvanishingLocus (s i))),
      (∀ i, Function.Surjective (MvPolynomial.eval₂Hom
        ((X.presheaf.map (homOfLE le_top).op).hom.comp c) (f i))) ∧
      ∃ N : ℕ, 0 < N ∧ ∃ t : ∀ i, K i → Γ(TauCeti.tensorPow L.obj N, ⊤),
        IsTensorPowExtension L s f N t := by
  have hcompact : IsCompact (Set.univ : Set X) := by
    have h := isCompact_iUnion fun i ↦ (hs i).isCompact
    simpa only [← Opens.coe_iSup, hcover, Opens.coe_top] using h
  have : CompactSpace X := isCompact_univ_iff.mp hcompact
  have : QuasiSeparatedSpace X :=
    Scheme.Modules.quasiSeparatedSpace_of_forall_isAffineOpen_nonvanishingLocus
      (fun x ↦ by
        have hx : x ∈ ⨆ i, L.obj.nonvanishingLocus (s i) := by rw [hcover]; trivial
        obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
        exact ⟨s i, hi, hs i⟩)
  choose K hK f hf using fun i ↦
    (hs i).exists_polynomial_generators c
  let _ (i : I) : Finite (K i) := hK i
  obtain ⟨N, hN, t, ht⟩ := L.exists_common_tensorPow_extensions s f
  exact ⟨K, hK, f, hf, N, hN, t, ht⟩

end TauCeti.AlgebraicGeometry.InvertibleSheaf
