/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.OpenPartialHomeomorph.Constructions
public import TauCeti.LinearAlgebra.Projectivization.Product
public import TauCeti.Topology.Algebra.Projectivization
public import TauCeti.Topology.PiCurry

/-!
# Standard product affine charts of multiprojective space as open partial homeomorphisms

Over a topological field `K`, a finite product `(i : ι) → ℙ K (Fin (n i + 1) → K)` of projective
spaces is covered by the standard product affine opens `Projectivization.piAffineOpen I`, which are
open in the product topology when `ι` is finite. Each flattened standard product affine chart
`Projectivization.piAffineChart I` is continuous on `piAffineOpen I` with continuous inverse, giving
an open partial homeomorphism `Projectivization.piAffineOpenPartialHomeomorph I` onto the flattened
coordinate space `(Σ i, Fin (n i)) → K`.

## Main declarations

* `Projectivization.isOpen_piAffineOpen`: for finite `ι`, each standard product affine open is open.
* `Projectivization.piAffineOpenPartialHomeomorph`: the standard product affine chart as an open
  partial homeomorphism onto `(Σ i, Fin (n i)) → K`.
* `Projectivization.isOpenEmbedding_piAffineChart_symm`: the inverse product chart is an open
  embedding.
* `Projectivization.interPiAffineOpenHomeomorph`: `piAffineChart I` identifies `X ∩ piAffineOpen I`
  homeomorphically with its coordinate image.
-/

public section

open Set Topology
open scoped LinearAlgebra.Projectivization

namespace Projectivization

section PiAffineOpen

variable {K : Type*} [DivisionRing K] [TopologicalSpace K] [T1Space K]
  {ι : Type*} [Finite ι] {κ : ι → Type*}

/-- For a finite index type `ι`, each standard product affine open of `(i : ι) → ℙ K (κ i → K)` is
open in the product topology. -/
theorem isOpen_piAffineOpen (I : ∀ i, κ i) : IsOpen (piAffineOpen (K := K) I) := by
  rw [piAffineOpen_def]
  exact isOpen_set_pi finite_univ fun i _ ↦ isOpen_affineOpen (I i)

end PiAffineOpen

section PiAffineChart

variable {K : Type*} [Field K] [TopologicalSpace K] {ι : Type*} {n : ι → ℕ}

/-- The inverse of a standard product affine chart is continuous. -/
theorem continuous_piAffineChart_symm (I : ∀ i, Fin (n i + 1)) :
    Continuous (piAffineChart (K := K) I).symm :=
  ((Continuous.piMap fun i ↦ continuous_affineChart_symm (I i)).comp
    (TauCeti.piCurryHomeomorph fun (_ : ι) (_ : Fin _) ↦ K).continuous).congr fun z ↦ by
      ext i
      have hcurry : TauCeti.piCurryHomeomorph (fun (_ : ι) (_ : Fin _) ↦ K) z i =
          fun k ↦ z ⟨i, k⟩ := by
        ext k
        simp
      simp [Pi.map, hcurry]

variable [ContinuousMul K] [ContinuousInv₀ K]

/-- A standard product affine chart is continuous on its domain `piAffineOpen I`. -/
theorem continuousOn_piAffineChart (I : ∀ i, Fin (n i + 1)) :
    ContinuousOn (piAffineChart (K := K) I) (piAffineOpen I) := by
  have hpi : ContinuousOn (Pi.map fun i ↦ (affineChart (K := K) (I i) : _ → Fin (n i) → K))
      (piAffineOpen I) := by
    rw [continuousOn_pi]
    intro i
    exact (continuousOn_affineChart (I i)).comp (continuous_apply i).continuousOn
      fun _ hp ↦ mem_piAffineOpen_iff.1 hp i
  exact ((TauCeti.piCurryHomeomorph fun (_ : ι) (_ : Fin _) ↦ K).symm.continuous.comp_continuousOn
    hpi).congr fun p _ ↦ by
      ext ⟨i, k⟩
      simp [Pi.map]

/-- **The affine part of a subset of multiprojective space.** The standard product affine chart at
`I` restricts to a homeomorphism from `X ∩ piAffineOpen I` onto its coordinate image `Z` in
`(Σ i, Fin (n i)) → K`. -/
noncomputable def interPiAffineOpenHomeomorph
    {X : Set ((i : ι) → ℙ K (Fin (n i + 1) → K))} {I : ∀ i, Fin (n i + 1)}
    {Z : Set ((Σ i, Fin (n i)) → K)} (hZ : piAffineChart I '' (X ∩ piAffineOpen I) = Z) :
    ↥(X ∩ piAffineOpen I) ≃ₜ Z :=
  ({ toPartialEquiv := piAffineChart I
     continuousOn_toFun := by simpa using continuousOn_piAffineChart I
     continuousOn_invFun := (continuous_piAffineChart_symm I).continuousOn } :
    PartialHomeomorph _ _).homeomorphOfImageSubsetSource (by simp) hZ

@[simp]
theorem coe_interPiAffineOpenHomeomorph_apply
    {X : Set ((i : ι) → ℙ K (Fin (n i + 1) → K))} {I : ∀ i, Fin (n i + 1)}
    {Z : Set ((Σ i, Fin (n i)) → K)} (hZ : piAffineChart I '' (X ∩ piAffineOpen I) = Z)
    (y : ↥(X ∩ piAffineOpen I)) :
    (interPiAffineOpenHomeomorph hZ y : (Σ i, Fin (n i)) → K) = piAffineChart I y := by
  simp [interPiAffineOpenHomeomorph, PartialHomeomorph.homeomorphOfImageSubsetSource,
    PartialHomeomorph.toFun', MapsTo.restrict, Subtype.map]

@[simp]
theorem coe_interPiAffineOpenHomeomorph_symm_apply
    {X : Set ((i : ι) → ℙ K (Fin (n i + 1) → K))} {I : ∀ i, Fin (n i + 1)}
    {Z : Set ((Σ i, Fin (n i)) → K)} (hZ : piAffineChart I '' (X ∩ piAffineOpen I) = Z)
    (z : Z) :
    ((interPiAffineOpenHomeomorph hZ).symm z : (i : ι) → ℙ K (Fin (n i + 1) → K)) =
      (piAffineChart I).symm z := by
  simp [interPiAffineOpenHomeomorph, PartialHomeomorph.homeomorphOfImageSubsetSource,
    PartialHomeomorph.toFun', PartialHomeomorph.symm, MapsTo.restrict, Subtype.map]

variable [T1Space K] [Finite ι]

/-- The standard product affine chart of `(i : ι) → ℙ K (Fin (n i + 1) → K)` at `I`, as an open
partial homeomorphism from `piAffineOpen I` onto `(Σ i, Fin (n i)) → K`. -/
noncomputable def piAffineOpenPartialHomeomorph (I : ∀ i, Fin (n i + 1)) :
    OpenPartialHomeomorph ((i : ι) → ℙ K (Fin (n i + 1) → K)) ((Σ i, Fin (n i)) → K) :=
  (OpenPartialHomeomorph.pi fun i ↦ affineOpenPartialHomeomorph (I i)).transHomeomorph
    (TauCeti.piCurryHomeomorph fun (_ : ι) (_ : Fin _) ↦ K).symm

@[simp]
theorem piAffineOpenPartialHomeomorph_toPartialEquiv (I : ∀ i, Fin (n i + 1)) :
    (piAffineOpenPartialHomeomorph (K := K) I).toPartialEquiv = piAffineChart I := by
  refine PartialEquiv.ext (fun p ↦ ?_) (fun z ↦ ?_) ?_
  · ext ⟨i, k⟩
    simp [piAffineOpenPartialHomeomorph]
  · ext i
    have hcurry : TauCeti.piCurryHomeomorph (fun (_ : ι) (_ : Fin _) ↦ K) z i =
        fun k ↦ z ⟨i, k⟩ := by
      ext k
      simp
    simp [piAffineOpenPartialHomeomorph, hcurry]
  · ext p
    simp [piAffineOpenPartialHomeomorph]

@[simp]
theorem coe_piAffineOpenPartialHomeomorph (I : ∀ i, Fin (n i + 1)) :
    ⇑(piAffineOpenPartialHomeomorph (K := K) I) = piAffineChart I := by
  rw [← OpenPartialHomeomorph.coe_toPartialEquiv, piAffineOpenPartialHomeomorph_toPartialEquiv]

@[simp]
theorem coe_piAffineOpenPartialHomeomorph_symm (I : ∀ i, Fin (n i + 1)) :
    ⇑(piAffineOpenPartialHomeomorph (K := K) I).symm = (piAffineChart I).symm := by
  rw [← OpenPartialHomeomorph.coe_toPartialEquiv_symm, piAffineOpenPartialHomeomorph_toPartialEquiv]

/-- For finite `ι`, the inverse of a standard product affine chart is an open embedding onto
`piAffineOpen I`. -/
theorem isOpenEmbedding_piAffineChart_symm (I : ∀ i, Fin (n i + 1)) :
    IsOpenEmbedding (piAffineChart (K := K) I).symm :=
  coe_piAffineOpenPartialHomeomorph_symm (K := K) I ▸
    (piAffineOpenPartialHomeomorph (K := K) I).symm.isOpenEmbedding (by simp)

end PiAffineChart

end Projectivization
