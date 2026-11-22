/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.ThricePuncturedSphere.FilledCover.AnalyticBelyiPair
public import TauCeti.Analysis.Complex.RiemannSurface.BelyiPair.Genus
public import TauCeti.Analysis.Complex.RiemannSurface.Branch.Sphere

/-!
# Genus and Riemann–Hurwitz for three-point covers

Reconciles `eulerChar` and `genus` of `AnalyticBelyiPair.{0}`, `ConnectedCover.toAnalyticBelyiPair`,
and `TopBranchedCover.{0} n` with their monodromy triples, proves the genus-form Riemann–Hurwitz
formulas, and derives `TopBranchedCover.instFiniteCWType`.
-/

public noncomputable section

open scoped OnePoint

namespace TauCeti

open ThricePuncturedSphere RiemannSurface

universe u

namespace AnalyticBelyiPair

section TypeZero

variable (P : AnalyticBelyiPair.{0}) {n : ℕ} (ν : P.restrict ⁻¹' {basePt} ≃ Fin n)

/-- **The Euler characteristic of an analytic Belyi pair is that of its monodromy triple.** -/
theorem eulerChar_X_eq_eulerChar_monodromyTriple :
    eulerChar P.X = (P.isCoveringMap_restrict.monodromyTriple ν).eulerChar := by
  linear_combination P.β.eulerChar_eq_two_mul_degree_sub_ramificationDegree -
    P.natCast_ramificationDegree_β_eq_two_mul_degree_sub_eulerChar ν

/-- **The topological genus of an analytic Belyi pair is the genus of its monodromy triple.** -/
theorem genus_X_eq_genus_monodromyTriple :
    genus P.X = (P.isCoveringMap_restrict.monodromyTriple ν).genus := by
  rw [genus_def, PermutationTriple.genus_def, P.eulerChar_X_eq_eulerChar_monodromyTriple ν]

/-- **Euler characteristic in terms of genus**: `eulerChar P.X = 2 - 2 * genus P.X`. -/
theorem eulerChar_X_eq_two_sub_two_mul_genus : eulerChar P.X = 2 - 2 * (genus P.X : ℤ) := by
  obtain ⟨ν'⟩ := P.nonempty_restrict_preimage_singleton_equiv basePt
  simp [P.eulerChar_X_eq_eulerChar_monodromyTriple ν', P.genus_X_eq_genus_monodromyTriple ν',
    (P.isCoveringMap_restrict.isConnected_monodromyTriple ν').two_sub_two_mul_genus]

/-- **Riemann–Hurwitz**: `2 * genus P.X - 2 = -2 * degree P.β + ramificationDegree P.β`. -/
theorem two_mul_genus_X_sub_two_eq :
    2 * (genus P.X : ℤ) - 2 = -2 * (degree P.β : ℤ) + ramificationDegree P.β := by
  linear_combination P.eulerChar_X_eq_two_sub_two_mul_genus -
    P.β.eulerChar_eq_two_mul_degree_sub_ramificationDegree

/-- **Riemann–Hurwitz in genus form**, with the target genus `genus (OnePoint ℂ)` written out. -/
theorem two_mul_genus_X_sub_two_eq_degree_mul_genus_onePoint :
    2 * (genus P.X : ℤ) - 2 =
      (degree P.β : ℤ) * (2 * (genus (OnePoint ℂ) : ℤ) - 2) + ramificationDegree P.β := by
  rw [genus_onePoint_complex]; linear_combination P.two_mul_genus_X_sub_two_eq

end TypeZero

end AnalyticBelyiPair

/-! ### Reconciliation on filled covers and topological branched covers -/

namespace ConnectedCover

variable {n : ℕ} (C : ConnectedCover (X := TopCat.of ThricePuncturedSphere) basePt n)

/-- The Euler characteristic of `C.toAnalyticBelyiPair.X` equals that of the monodromy triple. -/
theorem eulerChar_toAnalyticBelyiPair (ν : ⇑C.cover.proj ⁻¹' {basePt} ≃ Fin n) :
    eulerChar C.toAnalyticBelyiPair.X =
      (C.cover.isCoveringMap_proj.monodromyTriple ν).eulerChar := by
  obtain ⟨ν'⟩ := C.toAnalyticBelyiPair.nonempty_restrict_preimage_singleton_equiv basePt
  have h := C.isoClass_monodromyTriple_toAnalyticBelyiPair
    (ν'.trans (finCongr C.degree_toAnalyticBelyiPair)) ν
  rw [C.toAnalyticBelyiPair.eulerChar_X_eq_eulerChar_monodromyTriple _]
  exact PermutationTriple.eulerChar_eq_of_equivalent (PermutationTriple.IsoClass.mk_eq_mk_iff.1 h)

/-- The topological genus of `C.toAnalyticBelyiPair.X` equals that of the monodromy triple. -/
theorem genus_toAnalyticBelyiPair (ν : ⇑C.cover.proj ⁻¹' {basePt} ≃ Fin n) :
    genus C.toAnalyticBelyiPair.X = (C.cover.isCoveringMap_proj.monodromyTriple ν).genus := by
  rw [genus_def, PermutationTriple.genus_def, C.eulerChar_toAnalyticBelyiPair ν]

/-- **Reconciliation of the analytic and filled-cover ramification sums.** -/
theorem natCast_ramificationDegree_toAnalyticBelyiPair [Fintype (FilledPoint ⇑C.cover.proj)] :
    (ramificationDegree C.toAnalyticBelyiPair.β : ℤ) =
      ∑ i : FilledPoint ⇑C.cover.proj, ((FilledCover.degree ⇑C.cover.proj i : ℤ) - 1) := by
  obtain ⟨ν⟩ := C.nonempty_equiv_fin
  rw [FilledCover.sum_degree_sub_one C.cover.isCoveringMap_proj ν,
    ← C.eulerChar_toAnalyticBelyiPair ν]
  linear_combination C.toAnalyticBelyiPair.β.eulerChar_eq_two_mul_degree_sub_ramificationDegree +
    2 * congrArg ((↑) : ℕ → ℤ) C.degree_toAnalyticBelyiPair

end ConnectedCover

namespace TopBranchedCover

/-- Every topological branched cover `X : TopBranchedCover.{0} n` has finite CW type. -/
instance instFiniteCWType {n : ℕ} (X : TopBranchedCover.{0} n) : FiniteCWType X.Z :=
  X.exists_iso_toTopBranchedCover.elim fun P ⟨_, ⟨ι⟩⟩ ↦
    Homeomorph.finiteCWType (ι.toHomeomorph.trans (Homeomorph.refl P.X))

/-- Isomorphic topological branched covers have the same Euler characteristic. -/
theorem Iso.eulerChar_eq {n : ℕ} {X Y : TopBranchedCover.{u} n} [FiniteCWType X.Z]
    [FiniteCWType Y.Z] (ι : X.Iso Y) : eulerChar X.Z = eulerChar Y.Z := ι.toHomeomorph.eulerChar_eq

/-- Isomorphic topological branched covers have the same topological genus. -/
theorem Iso.genus_eq {n : ℕ} {X Y : TopBranchedCover.{u} n} [FiniteCWType X.Z] [FiniteCWType Y.Z]
    (ι : X.Iso Y) : genus X.Z = genus Y.Z := ι.toHomeomorph.toHomotopyEquiv.genus_eq

/-- **The Euler characteristic of a topological branched cover is that of its monodromy triple.** -/
theorem eulerChar_Z_eq_eulerChar_monodromyTriple {n : ℕ} (X : TopBranchedCover.{0} n)
    (ν : X.restrict ⁻¹' {basePt} ≃ Fin n) :
    eulerChar X.Z = (X.isCoveringMap_restrict.monodromyTriple ν).eulerChar := by
  obtain ⟨P, h, ⟨ι⟩⟩ := X.exists_iso_toTopBranchedCover
  obtain ⟨νP⟩ := P.nonempty_restrict_preimage_singleton_equiv basePt
  obtain ⟨νT⟩ := (P.toTopBranchedCover h).nonempty_restrict_preimage_singleton_equiv basePt
  rw [(ι.toHomeomorph.trans
      (Homeomorph.refl P.X : (P.toTopBranchedCover h).Z ≃ₜ P.X)).eulerChar_eq,
    P.eulerChar_X_eq_eulerChar_monodromyTriple (νP.trans (finCongr h))]
  exact PermutationTriple.eulerChar_eq_of_equivalent <| PermutationTriple.IsoClass.mk_eq_mk_iff.1 <|
    (P.isoClass_monodromyTriple_toTopBranchedCover h _ νT).symm.trans <|
      X.isCoveringMap_restrict.isoClass_monodromyTriple_eq_of_homeomorph ν
        (P.toTopBranchedCover h).isCoveringMap_restrict νT ι.restrict (funext ι.restrict_restrict)

/-- **The topological genus of a topological branched cover is that of its monodromy triple.** -/
theorem genus_Z_eq_genus_monodromyTriple {n : ℕ} (X : TopBranchedCover.{0} n)
    (ν : X.restrict ⁻¹' {basePt} ≃ Fin n) :
    genus X.Z = (X.isCoveringMap_restrict.monodromyTriple ν).genus := by
  rw [genus_def, PermutationTriple.genus_def, X.eulerChar_Z_eq_eulerChar_monodromyTriple ν]

/-- Every `X : TopBranchedCover.{0} n` satisfies `eulerChar X.Z = 2 - 2 * genus X.Z`. -/
theorem eulerChar_Z_eq_two_sub_two_mul_genus {n : ℕ} (X : TopBranchedCover.{0} n) :
    eulerChar X.Z = 2 - 2 * (genus X.Z : ℤ) := by
  obtain ⟨ν⟩ := X.nonempty_restrict_preimage_singleton_equiv basePt
  simp [X.eulerChar_Z_eq_eulerChar_monodromyTriple ν, X.genus_Z_eq_genus_monodromyTriple ν,
    (X.isCoveringMap_restrict.isConnected_monodromyTriple ν).two_sub_two_mul_genus]

/-- The Euler characteristic of an isomorphism class of topological branched covers. -/
def IsoClass.eulerChar {n : ℕ} : IsoClass.{0} n → ℤ :=
  IsoClass.lift (fun X ↦ TauCeti.eulerChar X.Z) fun _ _ ⟨ι⟩ ↦ ι.eulerChar_eq

/-- On the class of `X`, `IsoClass.eulerChar` evaluates to `eulerChar X.Z`. -/
@[simp] theorem IsoClass.eulerChar_mk {n : ℕ} (X : TopBranchedCover.{0} n) :
    (IsoClass.mk X).eulerChar = TauCeti.eulerChar X.Z := IsoClass.lift_mk _ _ X

/-- The topological genus of an isomorphism class of topological branched covers. -/
def IsoClass.genus {n : ℕ} : IsoClass.{0} n → ℕ :=
  IsoClass.lift (fun X ↦ RiemannSurface.genus X.Z) fun _ _ ⟨ι⟩ ↦ ι.genus_eq

/-- On the class of `X`, `IsoClass.genus` evaluates to `genus X.Z`. -/
@[simp] theorem IsoClass.genus_mk {n : ℕ} (X : TopBranchedCover.{0} n) :
    (IsoClass.mk X).genus = RiemannSurface.genus X.Z := IsoClass.lift_mk _ _ X

/-- `IsoClass.equivConnectedIsoClass` preserves the Euler characteristic. -/
@[simp] theorem IsoClass.eulerChar_equivConnectedIsoClass {n : ℕ} (c : IsoClass.{0} n) :
    (equivConnectedIsoClass n c).eulerChar = c.eulerChar := by
  obtain ⟨X, rfl⟩ := IsoClass.mk_surjective c
  exact (X.nonempty_restrict_preimage_singleton_equiv basePt).elim fun ν ↦ by
    simp [equivConnectedIsoClass_mk X ν, X.eulerChar_Z_eq_eulerChar_monodromyTriple ν]

/-- `IsoClass.equivConnectedIsoClass` preserves the genus. -/
@[simp] theorem IsoClass.genus_equivConnectedIsoClass {n : ℕ} (c : IsoClass.{0} n) :
    (equivConnectedIsoClass n c).genus = c.genus := by
  obtain ⟨X, rfl⟩ := IsoClass.mk_surjective c
  exact (X.nonempty_restrict_preimage_singleton_equiv basePt).elim fun ν ↦ by
    simp [equivConnectedIsoClass_mk X ν, X.genus_Z_eq_genus_monodromyTriple ν]

end TopBranchedCover

namespace AnalyticBelyiPair

/-- Forgetting the complex structure preserves the Euler characteristic. -/
@[simp] theorem eulerChar_toTopBranchedCover (P : AnalyticBelyiPair.{0}) {n : ℕ}
    (h : degree P.β = n) : eulerChar (P.toTopBranchedCover h).Z = eulerChar P.X :=
  (Homeomorph.refl P.X : (P.toTopBranchedCover h).Z ≃ₜ P.X).eulerChar_eq

/-- Forgetting the complex structure preserves the topological genus. -/
@[simp] theorem genus_toTopBranchedCover (P : AnalyticBelyiPair.{0}) {n : ℕ}
    (h : degree P.β = n) : genus (P.toTopBranchedCover h).Z = genus P.X :=
  (Homeomorph.refl P.X : (P.toTopBranchedCover h).Z ≃ₜ P.X).toHomotopyEquiv.genus_eq

/-- Passing to the underlying topological branched cover preserves the Euler characteristic. -/
@[simp] theorem eulerChar_toTopBranchedCoverIsoClass {n : ℕ} (P : Quotient (isoSetoid.{0} n)) :
    (toTopBranchedCoverIsoClass n P).eulerChar = isoClassEulerChar n P :=
  Quotient.inductionOn P fun _ ↦ by simp

/-- Passing to the underlying topological branched cover preserves the topological genus. -/
@[simp] theorem genus_toTopBranchedCoverIsoClass {n : ℕ} (P : Quotient (isoSetoid.{0} n)) :
    (toTopBranchedCoverIsoClass n P).genus = isoClassGenus n P :=
  Quotient.inductionOn P fun _ ↦ by simp

/-- The equivalence `isoClassEquivConnectedIsoClass` preserves the Euler characteristic. -/
@[simp] theorem eulerChar_isoClassEquivConnectedIsoClass {n : ℕ} (P : Quotient (isoSetoid.{0} n)) :
    (isoClassEquivConnectedIsoClass n P).eulerChar = isoClassEulerChar n P := by
  simp [← equivConnectedIsoClass_toTopBranchedCoverIsoClass]

/-- The equivalence `isoClassEquivConnectedIsoClass` preserves the genus. -/
@[simp] theorem genus_isoClassEquivConnectedIsoClass {n : ℕ} (P : Quotient (isoSetoid.{0} n)) :
    (isoClassEquivConnectedIsoClass n P).genus = isoClassGenus n P := by
  simp [← equivConnectedIsoClass_toTopBranchedCoverIsoClass]

end AnalyticBelyiPair

end TauCeti
