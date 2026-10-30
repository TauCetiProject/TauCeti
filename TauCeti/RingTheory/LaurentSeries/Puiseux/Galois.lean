/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Galois.Profinite
public import TauCeti.RingTheory.LaurentSeries.Puiseux.Kummer

/-!
# The Galois group of the Puiseux field over `K⸨X⸩`

The Tate module `lim_n μₙ(K) = TauCeti.PrimeToPTateModule 1 K` acts on the Puiseux field by the
Kummer automorphisms `t ^ (k / n) ↦ ζₙ ^ k t ^ (k / n)` (`TauCeti.puiseuxField.kummer`). This file
proves that, when `K` contains a primitive `n`-th root of unity for every `n > 0` (so `K` has
characteristic zero), these are all the automorphisms of the Puiseux field over `K⸨X⸩`, and that
the Kummer action is an isomorphism of topological groups for the Krull topology:

`Gal(puiseuxField K / K⸨X⸩) ≃ₜ* lim_n μₙ(K)`.

The inverse sends a Galois automorphism `σ` to the family of roots of unity by which its
restrictions to the levels `K⸨t ^ (1 / n)⸩` multiply `t ^ (1 / n)`. Each level is Galois over
`K⸨X⸩` with group `μₙ(K)` (`TauCeti.puiseuxField.levelGalEquivRootsOfUnity`), the restrictions to
levels `n ∣ m` are compatible along the power map `μₘ(K) → μₙ(K)`, and the levels exhaust the
Puiseux field. The Kummer action is continuous for any coefficient field: the finite-dimensional
intermediate fields defining the Krull topology are each contained in a level
(`IntermediateField.exists_le_level`).

When `K` is moreover algebraically closed, the Puiseux field is an algebraic closure of `K⸨X⸩`
(`TauCeti.puiseuxField.instIsAlgClosure`), so this identifies the absolute Galois group of
`K⸨X⸩` with `lim_n μₙ(K)`.

## Main definitions

* `TauCeti.puiseuxField.galEquivTateModule K`: the isomorphism of topological groups
  `Gal(puiseuxField K / K⸨X⸩) ≃ₜ* lim_n μₙ(K)`, inverse to the Kummer action.

## Main results

* `TauCeti.puiseuxField.continuous_kummer`: the Kummer action is continuous for the Krull
  topology, for every coefficient field.
* `TauCeti.puiseuxField.galEquivTateModule_symm_apply`: the inverse of `galEquivTateModule` is the
  Kummer action.
* `TauCeti.puiseuxField.proj_galEquivTateModule`: the level-`n` component of the image of `σ` is
  the root of unity of the restriction of `σ` to level `n`.
* `TauCeti.puiseuxField.apply_coe_level`: on level `n`, a Galois automorphism acts by the Kummer
  automorphism attached to the level-`n` component of its image.
* `TauCeti.puiseuxField.mem_fixingSubgroup_level_iff`: the automorphisms fixing level `n` are those
  whose image has trivial level-`n` component.
-/

public section

open IntermediateField
open scoped LaurentSeries

namespace TauCeti.puiseuxField

open PrimeToPTateModule

variable {K : Type*} [Field K]

/-- **Continuity of the Kummer action.** For every coefficient field `K`, the action of the Tate
module `lim_n μₙ(K)` on the Puiseux field is continuous for the Krull topology: a point whose
level-`n` component is trivial fixes level `n`, and every finite-dimensional intermediate field
lies in some level. -/
theorem continuous_kummer : Continuous (kummer K) := by
  refine continuous_of_continuousAt_one (kummer K) fun s hs ↦ ?_
  rw [map_one, krullTopology_mem_nhds_one_iff] at hs
  obtain ⟨E, _, hEs⟩ := hs
  obtain ⟨n, hn⟩ := E.exists_le_level
  -- The points with trivial level-`n` component form an open neighbourhood of `1` mapped into `s`.
  refine Filter.mem_map.2 <| Filter.mem_of_superset
    (((isLocallyConstant_proj ⟨n, n.ne_zero, Nat.coprime_one_right _⟩).isOpen_fiber 1).mem_nhds
      (map_one _)) fun ζ (hζ : proj ⟨n, n.ne_zero, Nat.coprime_one_right _⟩ ζ = 1) ↦
    hEs fun x ↦ ?_
  rw [AlgEquiv.smul_def]
  exact (kummer_coe_level ζ (⟨x, hn x.2⟩ : level K n)).trans
    (by rw [hζ, map_one, AlgEquiv.one_apply])

section RootsOfUnity

variable [∀ n : ℕ+, HasEnoughRootsOfUnity K n]

/-- The root of unity by which (the restriction to level `n` of) a Galois automorphism of the
Puiseux field multiplies `t ^ (1 / n)`. -/
private noncomputable def levelRootOfUnity (n : ℕ+) :
    Gal(puiseuxField K/K⸨X⸩) →* rootsOfUnity n K :=
  (levelGalEquivRootsOfUnity K n).toMonoidHom.comp (AlgEquiv.restrictNormalHom (level K n))

/-- The level-`n` root of unity of `σ` is the root of unity of its restriction to level `n`. -/
private theorem levelRootOfUnity_apply (n : ℕ+) (σ : Gal(puiseuxField K/K⸨X⸩)) :
    levelRootOfUnity n σ =
      levelGalEquivRootsOfUnity K n (AlgEquiv.restrictNormalHom (level K n) σ) :=
  rfl

/-- On level `n`, a Galois automorphism acts by the Kummer automorphism attached to its level-`n`
root of unity. -/
private theorem apply_coe_level_eq_levelKummer (σ : Gal(puiseuxField K/K⸨X⸩)) {n : ℕ+}
    (x : level K n) : σ x = levelKummer K n (levelRootOfUnity n σ) x := by
  rw [levelRootOfUnity_apply, ← levelGalEquivRootsOfUnity_symm_apply, MulEquiv.symm_apply_apply,
    AlgEquiv.restrictNormalHom_apply]

/-- The level roots of unity of a Galois automorphism are compatible along the power maps: for
`n ∣ m`, the level-`m` root raised to the power `m / n` is the level-`n` root. -/
private theorem levelRootOfUnity_pow_div (σ : Gal(puiseuxField K/K⸨X⸩)) {n m : ℕ+}
    (h : n ∣ m) : (levelRootOfUnity m σ : Kˣ) ^ ((m : ℕ) / n) = levelRootOfUnity n σ := by
  -- On level `n`, `σ` acts through level `m`, hence by the Kummer automorphism of the power.
  have hσ : AlgEquiv.restrictNormalHom (level K n) σ =
      levelKummer K n (rootsOfUnityPowOfDvd (PNat.dvd_iff.mp h) (levelRootOfUnity m σ)) := by
    refine AlgEquiv.ext fun x ↦ Subtype.ext ?_
    have hx := congrArg ((↑) : level K m → puiseuxField K)
      (levelKummer_inclusion h (levelRootOfUnity m σ) x)
    rw [← apply_coe_level_eq_levelKummer, coe_inclusion, coe_inclusion] at hx
    rw [AlgEquiv.restrictNormalHom_apply, hx]
  rw [levelRootOfUnity_apply n, hσ, levelGalEquivRootsOfUnity_levelKummer,
    coe_rootsOfUnityPowOfDvd_apply]

/-- The homomorphism from the Galois group of the Puiseux field to the Tate module whose level-`n`
component is the root of unity of the restriction to level `n`. -/
private noncomputable def toTateModule : Gal(puiseuxField K/K⸨X⸩) →* PrimeToPTateModule 1 K :=
  lift (fun m : {m : ℕ // m ≠ 0 ∧ m.Coprime 1} ↦
      levelRootOfUnity ((m : ℕ).toPNat (Nat.pos_of_ne_zero m.2.1)))
    fun m n σ h ↦ levelRootOfUnity_pow_div σ (n := (n : ℕ).toPNat (Nat.pos_of_ne_zero n.2.1))
      (m := (m : ℕ).toPNat (Nat.pos_of_ne_zero m.2.1)) (PNat.dvd_iff.mpr h)

/-- The level-`n` component of `toTateModule σ` is the level-`n` root of unity of `σ`. -/
private theorem proj_toTateModule (σ : Gal(puiseuxField K/K⸨X⸩)) (n : ℕ+) :
    proj ⟨n, n.ne_zero, Nat.coprime_one_right _⟩ (toTateModule σ) = levelRootOfUnity n σ :=
  -- `proj_lift` cannot be used by rewriting: the level-`m` component of `toTateModule` is
  -- `levelRootOfUnity (Nat.toPNat m _)`, whose codomain `μ_{Nat.toPNat m _}(K)` is `μ_m(K)` only up
  -- to unfolding `Nat.toPNat`. At `m = n` this index is `n` by eta for the subtype `ℕ+`.
  proj_lift _ _ _ σ

/-- The Kummer automorphism attached to the image of `σ` is `σ`: both act on each level `n` by the
Kummer automorphism of the level-`n` root of unity of `σ`, and the levels exhaust the Puiseux
field. -/
private theorem kummer_toTateModule (σ : Gal(puiseuxField K/K⸨X⸩)) :
    kummer K (toTateModule σ) = σ := by
  ext x : 1
  obtain ⟨n, hn⟩ := exists_mem_range_levelEmbedding x
  have hx : x ∈ level K n := (mem_level_iff K n x).mpr hn
  rw [kummer_coe_level _ (⟨x, hx⟩ : level K n), apply_coe_level_eq_levelKummer σ ⟨x, hx⟩,
    proj_toTateModule]

/-- The components of `toTateModule` are locally constant: each factors through the restriction to
a finite level, whose Galois group is discrete. -/
private theorem continuous_toTateModule : Continuous (toTateModule (K := K)) := by
  refine continuous_iff.2 fun m ↦ ?_
  have : FiniteDimensional K⸨X⸩ (level K ((m : ℕ).toPNat (Nat.pos_of_ne_zero m.2.1))) :=
    (levelPowerBasis K _).finite
  -- As in `proj_toTateModule`, the component is computed by `proj_lift` up to unfolding.
  have h : (fun σ ↦ proj m (toTateModule σ)) = fun σ ↦ levelGalEquivRootsOfUnity K _
      (AlgEquiv.restrictNormalHom (level K ((m : ℕ).toPNat (Nat.pos_of_ne_zero m.2.1))) σ) :=
    funext fun σ ↦ proj_lift _ _ m σ
  rw [h]
  exact (IsLocallyConstant.of_discrete _).comp_continuous
    (InfiniteGalois.restrictNormalHom_continuous _)

variable (K) in
/-- **The Galois group of the Puiseux field.** If `K` contains a primitive `n`-th root of unity
for every `n > 0`, the Galois group of the Puiseux field over `K⸨X⸩`, with its Krull topology, is
isomorphic as a topological group to the Tate module `lim_n μₙ(K)`. The inverse is the Kummer
action `t ^ (k / n) ↦ ζₙ ^ k t ^ (k / n)` (`TauCeti.puiseuxField.galEquivTateModule_symm_apply`),
and the level-`n` component of the image of `σ` is the root of unity by which `σ` multiplies
`t ^ (1 / n)` (`TauCeti.puiseuxField.proj_galEquivTateModule`). -/
noncomputable def galEquivTateModule :
    Gal(puiseuxField K/K⸨X⸩) ≃ₜ* PrimeToPTateModule 1 K where
  toFun := toTateModule
  invFun := kummer K
  left_inv := kummer_toTateModule
  right_inv ζ := kummer_injective (kummer_toTateModule (kummer K ζ))
  map_mul' := map_mul toTateModule
  continuous_toFun := continuous_toTateModule
  continuous_invFun := continuous_kummer

/-- `galEquivTateModule` is `toTateModule` as a function. -/
private theorem galEquivTateModule_apply (σ : Gal(puiseuxField K/K⸨X⸩)) :
    galEquivTateModule K σ = toTateModule σ :=
  rfl

/-- The inverse of `galEquivTateModule` is the Kummer action. -/
@[simp]
theorem galEquivTateModule_symm_apply (ζ : PrimeToPTateModule 1 K) :
    (galEquivTateModule K).symm ζ = kummer K ζ :=
  (rfl)

/-- The Kummer automorphism attached to the image of `σ` is `σ`. -/
@[simp]
theorem kummer_galEquivTateModule (σ : Gal(puiseuxField K/K⸨X⸩)) :
    kummer K (galEquivTateModule K σ) = σ :=
  kummer_toTateModule σ

/-- The image of the Kummer automorphism attached to `ζ` is `ζ`. -/
@[simp]
theorem galEquivTateModule_kummer (ζ : PrimeToPTateModule 1 K) :
    galEquivTateModule K (kummer K ζ) = ζ :=
  (galEquivTateModule K).apply_symm_apply ζ

/-- The level-`n` component of the image of `σ` is the root of unity attached by
`levelGalEquivRootsOfUnity` to the restriction of `σ` to level `n`. -/
theorem proj_galEquivTateModule (σ : Gal(puiseuxField K/K⸨X⸩)) (n : ℕ+) :
    proj ⟨n, n.ne_zero, Nat.coprime_one_right _⟩ (galEquivTateModule K σ) =
      levelGalEquivRootsOfUnity K n (AlgEquiv.restrictNormalHom (level K n) σ) := by
  rw [galEquivTateModule_apply, proj_toTateModule, levelRootOfUnity_apply]

/-- On level `n`, a Galois automorphism `σ` acts by the Kummer automorphism attached to the
level-`n` component of its image: it multiplies the coefficient of `t ^ (k / n)` by the `k`-th
power of that root of unity (`TauCeti.puiseuxField.coeff_levelKummer`). -/
theorem apply_coe_level (σ : Gal(puiseuxField K/K⸨X⸩)) {n : ℕ+} (x : level K n) :
    σ x = levelKummer K n
      (proj ⟨n, n.ne_zero, Nat.coprime_one_right _⟩ (galEquivTateModule K σ)) x := by
  rw [galEquivTateModule_apply, proj_toTateModule, apply_coe_level_eq_levelKummer]

/-- **The finite-level stabilizers.** A Galois automorphism fixes level `n` exactly when the
level-`n` component of its image in the Tate module is trivial. -/
theorem mem_fixingSubgroup_level_iff {σ : Gal(puiseuxField K/K⸨X⸩)} {n : ℕ+} :
    σ ∈ (level K n).fixingSubgroup ↔
      proj ⟨n, n.ne_zero, Nat.coprime_one_right _⟩ (galEquivTateModule K σ) = 1 := by
  rw [proj_galEquivTateModule, MulEquiv.map_eq_one_iff, ← MonoidHom.mem_ker,
    restrictNormalHom_ker]

end RootsOfUnity

end TauCeti.puiseuxField
