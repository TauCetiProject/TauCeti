/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.Isogeny.Power
public import TauCeti.LinearAlgebra.RootSystem.Positive
public import TauCeti.LinearAlgebra.RootSystem.Weyl.BasedAut

/-!
# Based endo-isogenies of root pairings

An endo-isogeny `f : RootPairingIsogeny P P` is *based* (`RootPairingIsogeny.IsBased b f`) relative
to `b : P.Base` if `f.indexEquiv` preserves `posRoots P b`, in which case it permutes `posRoots P b`
bijectively (`IsBased.image_posRoots`). Based endo-isogenies are closed under `id`, `1`, `comp`,
`*`, and `^`, contain `smulId P c` (`isBased_smulId`), and are invariant under right multiplication
by `smulId P c` (`isBased_mul_smulId_iff`), while no reflection is based
(`not_isBased_ofEquiv_reflection`). For finite crystallographic pairings over a char-zero domain,
`(ofEquiv g).IsBased b ↔ g ∈ b.basedAut` (`isBased_ofEquiv_iff`).

## References

* R. Steinberg, *Endomorphisms of Linear Algebraic Groups*, Mem. Amer. Math. Soc. **80** (1968),
  §11; Schémas en groupes (SGA 3), Exposé XXI, §6.8.
-/

public section

namespace TauCeti.RootPairingIsogeny
variable {ι R M N : Type*} [CommRing R] [CharZero R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] {P : RootPairing ι R M N}

/-- **A based endo-isogeny relative to `b`**: `f.indexEquiv` preserves `posRoots P b`. -/
def IsBased (b : P.Base) (f : RootPairingIsogeny P P) : Prop :=
  Set.MapsTo f.indexEquiv (posRoots P b) (posRoots P b)

/-- Unfolding characterization of `RootPairingIsogeny.IsBased`. -/
theorem isBased_def (b : P.Base) (f : RootPairingIsogeny P P) :
    f.IsBased b ↔ Set.MapsTo f.indexEquiv (posRoots P b) (posRoots P b) := Iff.rfl

/-- A based endo-isogeny sends every positive root index to a positive root index. -/
theorem IsBased.indexEquiv_mem_posRoots {b : P.Base} {f : RootPairingIsogeny P P}
    (hf : f.IsBased b) {i : ι} (hi : i ∈ posRoots P b) : f.indexEquiv i ∈ posRoots P b :=
  (isBased_def b f).mp hf hi

/-- The identity isogeny `RootPairingIsogeny.id P` is based for every base `b`. -/
@[simp] theorem isBased_id (b : P.Base) : (RootPairingIsogeny.id P).IsBased b := by
  rw [isBased_def, id_indexEquiv]; exact Set.mapsTo_id _

/-- The multiplicative unit `1 : RootPairingIsogeny P P` is based for every base `b`. -/
@[simp] theorem isBased_one (b : P.Base) : (1 : RootPairingIsogeny P P).IsBased b := by
  rw [one_def]; exact isBased_id b

/-- Based endo-isogenies are closed under `RootPairingIsogeny.comp`. -/
theorem IsBased.comp {b : P.Base} {g f : RootPairingIsogeny P P} (hg : g.IsBased b)
    (hf : f.IsBased b) : (g.comp f).IsBased b := by
  rw [isBased_def, comp_indexEquiv]; exact ((isBased_def b g).mp hg).comp ((isBased_def b f).mp hf)

/-- Based endo-isogenies are closed under composition (`*`). -/
theorem IsBased.mul {b : P.Base} {f g : RootPairingIsogeny P P} (hf : f.IsBased b)
    (hg : g.IsBased b) : (f * g).IsBased b := by rw [mul_def]; exact hf.comp hg

/-- Based endo-isogenies are closed under natural-number powers. -/
theorem IsBased.pow {b : P.Base} {f : RootPairingIsogeny P P} (hf : f.IsBased b) (n : ℕ) :
    (f ^ n).IsBased b := by
  induction n with
  | zero => rw [pow_zero]; exact isBased_one b
  | succ n ih => rw [pow_succ']; exact hf.mul ih

/-- Every based endo-isogeny maps `posRoots P b` bijectively onto itself. -/
@[simp] theorem IsBased.image_posRoots {b : P.Base} {f : RootPairingIsogeny P P}
    (hf : f.IsBased b) : f.indexEquiv '' posRoots P b = posRoots P b := by
  refine Set.Subset.antisymm ((isBased_def b f).mp hf).image_subset fun j hj => ?_
  let i := f.indexEquiv.symm j; refine ⟨i, ?_, f.indexEquiv.apply_symm_apply j⟩
  by_contra hi; let ineg := P.reflectionPerm i i
  have hipos : ineg ∈ posRoots P b := (reflectionPerm_self_mem_posRoots_iff_mem_negRoots P b i).mpr
    ((not_mem_posRoots_iff_mem_negRoots P b i).mp hi)
  have hsum := congrArg f.weightMap (by
    rw [RootPairing.root_reflectionPerm, RootPairing.reflection_apply_self, add_neg_cancel] :
    P.root i + P.root ineg = 0)
  rw [map_add, map_zero, f.root_weightMap, f.root_weightMap, f.indexEquiv.apply_symm_apply,
    ← Int.toNat_of_nonneg (f.exponent_pos i).le, ← Int.toNat_of_nonneg (f.exponent_pos ineg).le]
    at hsum
  simp only [Int.cast_natCast, Nat.cast_smul_eq_nsmul] at hsum
  rw [← Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (Int.lt_toNat.mpr (f.exponent_pos i)).ne'),
    add_smul, one_smul, add_comm _ (P.root j), add_assoc] at hsum
  exact root_add_ne_zero_of_mem_posRoots_of_mem_posRootCone P b hj (AddSubmonoid.add_mem _
    (AddSubmonoid.nsmul_mem _ (root_mem_posRootCone_of_mem_posRoots P b hj) _)
    (AddSubmonoid.nsmul_mem _
      (root_mem_posRootCone_of_mem_posRoots P b (hf.indexEquiv_mem_posRoots hipos)) _)) hsum

/-- An endo-isogeny is based iff `f.indexEquiv '' posRoots P b = posRoots P b`. -/
theorem isBased_iff_image_posRoots (b : P.Base) (f : RootPairingIsogeny P P) :
    f.IsBased b ↔ f.indexEquiv '' posRoots P b = posRoots P b :=
  ⟨IsBased.image_posRoots, fun h => (isBased_def b f).mpr (Set.mapsTo_iff_image_subset.mpr h.le)⟩

/-- The inverse index bijection of a based endo-isogeny preserves `posRoots P b`. -/
theorem IsBased.indexEquiv_symm_mem_posRoots {b : P.Base} {f : RootPairingIsogeny P P}
    (hf : f.IsBased b) {j : ι} (hj : j ∈ posRoots P b) : f.indexEquiv.symm j ∈ posRoots P b := by
  rw [← hf.image_posRoots] at hj; rcases hj with ⟨i, hi, rfl⟩; simpa using hi

/-- A based endo-isogeny maps a root index into `posRoots P b` iff the root index is positive. -/
-- Note: `@[simp]` is on `isPos_indexEquiv_iff` because `TauCeti.mem_posRoots` simplifies
-- `∈ posRoots P b` to `b.IsPos`.
theorem IsBased.indexEquiv_mem_posRoots_iff {b : P.Base} {f : RootPairingIsogeny P P}
    (hf : f.IsBased b) {i : ι} : f.indexEquiv i ∈ posRoots P b ↔ i ∈ posRoots P b :=
  ⟨fun h => by simpa using hf.indexEquiv_symm_mem_posRoots h, hf.indexEquiv_mem_posRoots⟩

/-- A based endo-isogeny preserves `b.IsPos` on root indices. -/
@[simp] theorem IsBased.isPos_indexEquiv_iff {b : P.Base} {f : RootPairingIsogeny P P}
    (hf : f.IsBased b) {i : ι} : b.IsPos (f.indexEquiv i) ↔ b.IsPos i := by
  simp only [← mem_posRoots]
  exact hf.indexEquiv_mem_posRoots_iff

/-- An automorphism `ofEquiv g` is based iff `g.indexEquiv` maps `posRoots P b` into itself. -/
theorem isBased_ofEquiv_iff_mapsTo (b : P.Base) (g : P.Aut) :
    (ofEquiv g).IsBased b ↔ Set.MapsTo g.indexEquiv (posRoots P b) (posRoots P b) := by
  rw [isBased_def, ofEquiv_indexEquiv]

/-- **No reflection automorphism is based**, relative to any base `b`. -/
@[simp] theorem not_isBased_ofEquiv_reflection (b : P.Base) (i : ι) :
    ¬ (ofEquiv (RootPairing.Equiv.reflection P i)).IsBased b := fun h => by
  by_cases hi : i ∈ posRoots P b
  · exact reflectionPerm_self_notMem_posRoots P b hi (by simpa using h.indexEquiv_mem_posRoots hi)
  · have hneg : P.reflectionPerm i i ∈ posRoots P b :=
      (reflectionPerm_self_mem_posRoots_iff_mem_negRoots P b i).mpr
        ((not_mem_posRoots_iff_mem_negRoots P b i).mp hi)
    exact hi (by simpa [P.reflectionPerm_self] using h.indexEquiv_mem_posRoots hneg)

/-- For a finite crystallographic pairing over a char-zero domain, `ofEquiv g` is based iff
`g ∈ b.basedAut`. -/
@[simp] theorem isBased_ofEquiv_iff [Finite ι] [IsDomain R] [P.IsCrystallographic]
    (b : P.Base) (g : P.Aut) : (ofEquiv g).IsBased b ↔ g ∈ b.basedAut := by
  rw [isBased_iff_image_posRoots, ofEquiv_indexEquiv,
    RootPairing.Base.mem_basedAut_iff_image_posRoots]

section Int
variable {ι M N : Type*} [AddCommGroup M] [Module.Free ℤ M] [Module.Finite ℤ M]
  [AddCommGroup N] [Module.Free ℤ N] [Module.Finite ℤ N]

/-- Every positive integer scaling `smulId P c` is based for every base `b : P.Base`. -/
@[simp] theorem isBased_smulId (P : RootPairing ι ℤ M N) (b : P.Base) (c : ℕ+) :
    (smulId P c).IsBased b := by rw [isBased_def, smulId_indexEquiv]; exact Set.mapsTo_id _

/-- Right multiplication by a positive integer scaling preserves basedness. -/
@[simp] theorem isBased_mul_smulId_iff {P : RootPairing ι ℤ M N} (b : P.Base)
    (f : RootPairingIsogeny P P) (c : ℕ+) : (f * smulId P c).IsBased b ↔ f.IsBased b := by
  rw [isBased_def, isBased_def, indexEquiv_mul, smulId_indexEquiv, Equiv.refl_trans]

end Int
end TauCeti.RootPairingIsogeny
