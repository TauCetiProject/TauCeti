/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.CrossedProduct.Comparison
public import TauCeti.FieldTheory.GaloisCohomology.MuTwo.BrauerTorsion

/-!
# The `2`-torsion of the Brauer group as `H²(G_K, 𝔽₂)`

Let `K` be a field in which `2` is invertible. This file identifies the `2`-torsion subgroup
`Br(K)[2]` of the Brauer group with continuous cohomology of the absolute Galois group with
trivial `𝔽₂` coefficients,

```text
brauer2EquivH2 K : Additive Br(K)[2] ≃+ H²_cont(G_K, 𝔽₂),
```

which in classical notation is `Br(K)[2] ≃ H²(G_K, μ₂)`.

The identification is assembled from two maps already available. The comparison
`TauCeti.brauerCohomologyEquiv K : Additive (Br K) ≃+ H²_cont(G_K, (Kˢ)ˣ)` identifies the whole
Brauer group with cohomology with multiplicative coefficients, and the Kummer map
`TauCeti.h2MuToUnits K : H²_cont(G_K, 𝔽₂) → H²_cont(G_K, (Kˢ)ˣ)` is injective with image the
`2`-torsion (`TauCeti.h2MuToUnits_injective`, `TauCeti.h2MuToUnits_range`). An additive
equivalence carries `2`-torsion onto `2`-torsion, so the two `2`-torsion subgroups match.

The identification has no normalization of its own: it is the unique additive equivalence making
the square

```text
Br(K)[2]  ─────── brauer2EquivH2 ──────→  H²_cont(G_K, 𝔽₂)
   │                                            │
   │ inclusion                                  │ h2MuToUnits
   ↓                                            ↓
 Br(K)  ─────── brauerCohomologyEquiv ───→  H²_cont(G_K, (Kˢ)ˣ)
```

commute (`TauCeti.brauer2EquivH2_h2MuToUnits`, `TauCeti.brauer2EquivH2_unique`), so every
statement about it is a statement about `TauCeti.brauerCohomologyEquiv` read through the injective
map `TauCeti.h2MuToUnits`.

## Main definitions

* `TauCeti.BrauerGroup.twoTorsion K`: the subgroup `Br(K)[2]` of classes whose square is trivial.
* `TauCeti.brauer2EquivH2 K`: the identification `Additive Br(K)[2] ≃+ H²_cont(G_K, 𝔽₂)`.

## Main results

* `TauCeti.brauer2EquivH2_h2MuToUnits`: the square above commutes.
* `TauCeti.brauer2EquivH2_unique`: the commuting square determines the identification.
* `TauCeti.brauer2EquivH2_symm_apply`: the inverse identification sends a class `y` to the Brauer
  class corresponding to `h2MuToUnits K y` under the comparison.

## References

* P. Gille and T. Szamuely, *Central Simple Algebras and Galois Cohomology* (2006), §4.4.
* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, second edition,
  (6.2.1) and the exact sequence following it.
-/

public section

noncomputable section

namespace TauCeti

universe u

namespace BrauerGroup

variable (K : Type u) [Field K]

/-- **The `2`-torsion of the Brauer group**, `Br(K)[2]`: the classes whose square is trivial,
as the kernel of squaring. -/
def twoTorsion : Subgroup (BrauerGroup.{u, u} K) :=
  (powMonoidHom 2 : BrauerGroup.{u, u} K →* BrauerGroup.{u, u} K).ker

variable {K} in
/-- A Brauer class is `2`-torsion exactly when its square is trivial. -/
@[simp]
theorem mem_twoTorsion {x : BrauerGroup.{u, u} K} : x ∈ twoTorsion K ↔ x ^ 2 = 1 :=
  MonoidHom.mem_ker

end BrauerGroup

variable (K : Type) [Field K]

open BrauerGroup

variable [Invertible (2 : K)]

/-- The Brauer class corresponding to `h2MuToUnits K y` under the comparison
`brauerCohomologyEquiv K` is `2`-torsion, because `h2MuToUnits K y` is. -/
private theorem toMul_brauerCohomologyEquiv_symm_h2MuToUnits_mem_twoTorsion
    (y : continuousCohomology 2 (trivialF2 (AbsoluteGaloisGroup K))) :
    ((brauerCohomologyEquiv K).symm ((h2MuToUnits K).hom y)).toMul ∈ twoTorsion K := by
  rw [mem_twoTorsion, sq, ← toMul_add, ← map_add, (h2MuToUnits_range K _).1 ⟨y, rfl⟩, map_zero,
    toMul_zero]

/-- The inverse direction of `brauer2EquivH2`: a class of `H²_cont(G_K, 𝔽₂)` goes to the
`2`-torsion Brauer class corresponding to its image under `h2MuToUnits K`. -/
private def h2ToTwoTorsion :
    continuousCohomology 2 (trivialF2 (AbsoluteGaloisGroup K)) →+ Additive (twoTorsion K) where
  toFun y := Additive.ofMul
    ⟨_, toMul_brauerCohomologyEquiv_symm_h2MuToUnits_mem_twoTorsion K y⟩
  map_zero' := by
    ext
    simp
  map_add' y z := by
    ext
    simp

/-- The image of a class under `h2ToTwoTorsion`, read in the Brauer group. -/
private theorem coe_toMul_h2ToTwoTorsion
    (y : continuousCohomology 2 (trivialF2 (AbsoluteGaloisGroup K))) :
    ((h2ToTwoTorsion K y).toMul : BrauerGroup K) =
      ((brauerCohomologyEquiv K).symm ((h2MuToUnits K).hom y)).toMul :=
  rfl

/-- `h2ToTwoTorsion` is bijective: it is injective because `h2MuToUnits K` and the comparison
are, and surjective because every `2`-torsion class of `H²_cont(G_K, (Kˢ)ˣ)` is in the image of
`h2MuToUnits K`. -/
private theorem h2ToTwoTorsion_bijective : Function.Bijective (h2ToTwoTorsion K) := by
  refine ⟨fun y z h ↦ h2MuToUnits_injective K ((brauerCohomologyEquiv K).symm.injective ?_), ?_⟩
  · have h' := congrArg (fun x ↦ ((Additive.toMul x : twoTorsion K) : BrauerGroup K)) h
    simpa only [coe_toMul_h2ToTwoTorsion, EmbeddingLike.apply_eq_iff_eq] using h'
  · intro x
    have hx : brauerCohomologyEquiv K (Additive.ofMul (x.toMul : BrauerGroup K)) +
        brauerCohomologyEquiv K (Additive.ofMul (x.toMul : BrauerGroup K)) = 0 := by
      rw [← map_add, ← ofMul_mul, ← sq, mem_twoTorsion.1 x.toMul.2, ofMul_one, map_zero]
    obtain ⟨y, hy⟩ := (h2MuToUnits_range K _).2 hx
    refine ⟨y, ?_⟩
    apply Additive.toMul.injective
    ext
    rw [coe_toMul_h2ToTwoTorsion, hy, AddEquiv.symm_apply_apply, toMul_ofMul]

/-- **The `2`-torsion of the Brauer group is `H²(G_K, 𝔽₂)`.** The identification
`Br(K)[2] ≃ H²_cont(G_K, 𝔽₂)`, with multiplication of Brauer classes going to addition of
cohomology classes; classically `Br(K)[2] ≃ H²(G_K, μ₂)`. It is characterized by
`brauer2EquivH2_h2MuToUnits`: followed by `h2MuToUnits K`, it is the comparison
`brauerCohomologyEquiv K` on `2`-torsion classes; see `brauer2EquivH2_unique`. -/
def brauer2EquivH2 :
    Additive (twoTorsion K) ≃+ continuousCohomology 2 (trivialF2 (AbsoluteGaloisGroup K)) :=
  (AddEquiv.ofBijective (h2ToTwoTorsion K) (h2ToTwoTorsion_bijective K)).symm

/-- The inverse identification sends a class `y` of `H²_cont(G_K, 𝔽₂)` to the Brauer class that
the comparison `brauerCohomologyEquiv K` matches with `h2MuToUnits K y`. -/
@[simp]
theorem brauer2EquivH2_symm_apply
    (y : continuousCohomology 2 (trivialF2 (AbsoluteGaloisGroup K))) :
    (((brauer2EquivH2 K).symm y).toMul : BrauerGroup K) =
      ((brauerCohomologyEquiv K).symm ((h2MuToUnits K).hom y)).toMul :=
  coe_toMul_h2ToTwoTorsion K y

variable {K}

/-- **The normalization of the `2`-torsion comparison.** On a `2`-torsion Brauer class,
`brauer2EquivH2 K` followed by `h2MuToUnits K` is the comparison `brauerCohomologyEquiv K`. -/
@[simp]
theorem brauer2EquivH2_h2MuToUnits (x : twoTorsion K) :
    (h2MuToUnits K).hom (brauer2EquivH2 K (Additive.ofMul x)) =
      brauerCohomologyEquiv K (Additive.ofMul (x : BrauerGroup K)) := by
  have h := brauer2EquivH2_symm_apply K (brauer2EquivH2 K (Additive.ofMul x))
  rw [AddEquiv.symm_apply_apply, toMul_ofMul] at h
  rw [h, ofMul_toMul, AddEquiv.apply_symm_apply]

/-- **The `2`-torsion comparison is determined by its normalization.** Any additive equivalence
`Br(K)[2] ≃ H²_cont(G_K, 𝔽₂)` which, followed by `h2MuToUnits K`, is the comparison
`brauerCohomologyEquiv K` on `2`-torsion classes is `brauer2EquivH2 K`, because `h2MuToUnits K`
is injective. -/
theorem brauer2EquivH2_unique
    (e : Additive (twoTorsion K) ≃+ continuousCohomology 2 (trivialF2 (AbsoluteGaloisGroup K)))
    (h : ∀ x : twoTorsion K, (h2MuToUnits K).hom (e (Additive.ofMul x)) =
      brauerCohomologyEquiv K (Additive.ofMul (x : BrauerGroup K))) :
    e = brauer2EquivH2 K :=
  AddEquiv.ext fun x ↦ h2MuToUnits_injective K
    ((h x.toMul).trans (brauer2EquivH2_h2MuToUnits x.toMul).symm)

end TauCeti
