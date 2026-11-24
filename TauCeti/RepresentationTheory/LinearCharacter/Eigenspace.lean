/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Exact.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.RepresentationTheory.Intertwining
public import Mathlib.RepresentationTheory.Invariants
public import TauCeti.RepresentationTheory.Character.Twist
import TauCeti.RepresentationTheory.Invariants

/-!
# Character eigensubmodules and character sums

Let `ρ` be a representation of a group `G` on a module `V` over a commutative ring `k`, and let
`χ : G →* kˣ` be a linear character. The **`χ`-eigensubmodule** of `ρ` is

`V^χ = {v ∈ V | ρ g v = χ(g) v for all g ∈ G}`,

here `Representation.charEigenspace ρ χ`, the intersection of the Mathlib eigenspaces
`Module.End.eigenspace (ρ g) (χ g)`. It needs neither a finite group nor any invertibility in `k`.
Since every value of `χ` is a unit, `V^χ` is the space of invariants of the twist of `ρ` by
`χ⁻¹`, Tau Ceti's `Representation.charTwist χ⁻¹ ρ`, and the trivial character gives Mathlib's
`Representation.invariants`.

For a finite group, the **character sum** of `χ` is the operator

`S_χ(v) = ∑_{g ∈ G} χ(g)⁻¹ ρ(g) v`,

here `Representation.charSum ρ χ`. It is unnormalised: it is the group sum `Representation.norm`
of the twist by `χ⁻¹`, and is defined whatever the order of `G`. Moving `ρ g` through the sum
rescales it by `χ(g)`, so `S_χ` takes values in `V^χ`, acts on `V^χ` as multiplication by `#G`, and
satisfies `S_χ ∘ S_χ = #G • S_χ`. When `#G` is a unit of `k`, its range is all of `V^χ`. A
consequence of the translation law is the identity `S_χ(u - ρ(φ⁻¹) u) = (1 - χ(φ)⁻¹) S_χ(u)`,
which turns the Euler factor `1 - Fr⁻¹` of a norm relation into the scalar `1 - χ(Fr)⁻¹`.

Intertwining maps carry `V^χ` into `W^χ` and commute with character sums, so `V ↦ V^χ` is a
functor (`Representation.IntertwiningMap.charEigenspaceMap`). It preserves injections, and when
`#G` is a unit of `k` it is exact: a preimage of a vector of `W^χ` is moved into `V^χ` by the
normalised character sum. Without this hypothesis exactness fails, already for the invariants of
the regular representation of a group of order `p` over `𝔽_p`.

These are the character components used in Euler system arguments, for instance for
`(L^× ⊗ O)^χ` with `Δ = Gal(L/ℚ)`, and the character sums producing the cyclotomic generators of
those components.

## Main definitions

* `Representation.charEigenspace ρ χ`: the `χ`-eigensubmodule `V^χ`.
* `Representation.IntertwiningMap.charEigenspaceMap f χ`: the restriction `V^χ → W^χ` of an
  intertwining map.
* `Representation.charSum ρ χ`: the character sum `v ↦ ∑ g, χ(g)⁻¹ ρ(g) v`.

## Main results

* `Representation.mem_charEigenspace_iff`: `v ∈ V^χ` iff `ρ g v = χ(g) v` for all `g`.
* `Representation.charEigenspace_eq_invariants_charTwist`: `V^χ` is the space of invariants of the
  twist of `ρ` by `χ⁻¹`; `Representation.charEigenspace_one`: the trivial character gives the
  invariants.
* `Representation.charEigenspace_eq_bot`: if some `g` acts trivially and `χ(g) - 1` acts
  injectively on `V`, then `V^χ = 0`.
* `Representation.charSum_apply_mem`, `Representation.charSum_apply_of_mem`,
  `Representation.charSum_comp_charSum`: `S_χ` lands in `V^χ`, is `#G` on `V^χ`, and squares to
  `#G • S_χ`.
* `Representation.charSum_self_apply`, `Representation.charSum_sub_self_inv_apply`: the translation
  law and the Euler-factor identity.
* `Representation.IntertwiningMap.map_charSum`: intertwining maps commute with character sums.
* `Representation.range_charSum`: when `#G` is a unit, the range of `S_χ` is `V^χ`.
* `Representation.IntertwiningMap.charEigenspaceMap_surjective` and
  `Representation.IntertwiningMap.exact_charEigenspaceMap`: when `#G` is a unit, `V ↦ V^χ`
  preserves surjections and exact sequences.

## References

* K. Rubin, *Euler Systems*, Annals of Mathematics Studies 147 (2000), Chapter I, §6.2,
  Definition 6.2, and Chapter III, §2.2, display (4), and the proof of Theorem 2.3, display (6).
-/

public section

namespace Representation

open Module

variable {k G V W U : Type*} [CommRing k] [AddCommGroup V] [Module k V] [AddCommGroup W]
  [Module k W] [AddCommGroup U] [Module k U]

section Monoid

variable [Monoid G] (ρ : Representation k G V) {σ : Representation k G W}
  {τ : Representation k G U} (χ : G →* kˣ)

/-- **The `χ`-eigensubmodule** `V^χ = {v | ρ g v = χ(g) v for all g}` of a representation `ρ`,
for a linear character `χ : G →* kˣ`: the intersection of the eigenspaces of the operators
`ρ g` for the eigenvalues `χ g`. -/
def charEigenspace : Submodule k V :=
  ⨅ g, End.eigenspace (ρ g) (χ g : k)

/-- The `χ`-eigensubmodule is the intersection of the eigenspaces `Eig(ρ g, χ g)`. -/
theorem charEigenspace_def : ρ.charEigenspace χ = ⨅ g, End.eigenspace (ρ g) (χ g : k) :=
  (rfl)

/-- A vector lies in the `χ`-eigensubmodule exactly when every `ρ g` acts on it by `χ g`. -/
@[simp]
theorem mem_charEigenspace_iff {v : V} :
    v ∈ ρ.charEigenspace χ ↔ ∀ g, ρ g v = (χ g : k) • v := by
  simp only [charEigenspace, Submodule.mem_iInf, End.mem_eigenspace_iff]

/-- The `χ`-eigensubmodule is the intersection of the kernels of the operators `ρ g - χ(g)`. -/
theorem charEigenspace_eq_iInf_ker :
    ρ.charEigenspace χ = ⨅ g, LinearMap.ker (ρ g - (χ g : k) • 1) := by
  simp only [charEigenspace, End.eigenspace_def]

/-- A vector lies in the `χ`-eigensubmodule exactly when `χ(g)⁻¹ ρ(g)` fixes it for every `g`. -/
theorem mem_charEigenspace_iff_inv_smul {v : V} :
    v ∈ ρ.charEigenspace χ ↔ ∀ g, (((χ g)⁻¹ : kˣ) : k) • ρ g v = v := by
  rw [mem_charEigenspace_iff]
  refine forall_congr' fun g => ⟨fun h => ?_, fun h => ?_⟩
  · rw [h, smul_smul, Units.inv_mul, one_smul]
  · conv_rhs => rw [← h]
    rw [smul_smul, Units.mul_inv, one_smul]

/-- **A trivially acting element with nontrivial character kills the eigensubmodule.** If `ρ g`
is the identity and multiplication by `χ(g) - 1` is injective on `V`, then `V^χ = 0`. Injectivity
on `V` itself is needed, not just `χ(g) ≠ 1`: the trivial action of a group of order two on
`ℤ/2` has `V^χ = V` for the sign character `χ` with values in `ℤ`. -/
theorem charEigenspace_eq_bot {g : G} (hg : ∀ v, ρ g v = v)
    (hinj : Function.Injective fun v : V => ((χ g : k) - 1) • v) :
    ρ.charEigenspace χ = ⊥ := by
  refine (Submodule.eq_bot_iff _).2 fun v hv => hinj ?_
  have := (ρ.mem_charEigenspace_iff χ).1 hv g
  simp only [sub_smul, one_smul, smul_zero, ← this, hg, sub_self]

namespace IntertwiningMap

variable {ρ}

/-- **Intertwining maps preserve eigensubmodules**: an intertwining map `f : ρ → σ` carries
`V^χ` into `W^χ`. -/
theorem apply_mem_charEigenspace (f : IntertwiningMap ρ σ) {v : V}
    (hv : v ∈ ρ.charEigenspace χ) : f v ∈ σ.charEigenspace χ := by
  rw [mem_charEigenspace_iff] at hv ⊢
  intro g
  rw [← f.isIntertwining, hv, map_smul]

/-- The restriction `V^χ → W^χ` of an intertwining map `f : ρ → σ`. -/
def charEigenspaceMap (f : IntertwiningMap ρ σ) :
    ρ.charEigenspace χ →ₗ[k] σ.charEigenspace χ :=
  f.toLinearMap.restrict fun _ => f.apply_mem_charEigenspace χ

/-- The restriction of `f` to `V^χ` acts as `f`. -/
@[simp]
theorem coe_charEigenspaceMap_apply (f : IntertwiningMap ρ σ) (v : ρ.charEigenspace χ) :
    (f.charEigenspaceMap χ v : W) = f v :=
  (rfl)

/-- The identity restricts to the identity of `V^χ`. -/
@[simp]
theorem charEigenspaceMap_id : (IntertwiningMap.id ρ).charEigenspaceMap χ = LinearMap.id :=
  (rfl)

/-- Restriction to `χ`-eigensubmodules is compatible with composition. -/
theorem charEigenspaceMap_comp (f : IntertwiningMap σ τ) (f' : IntertwiningMap ρ σ) :
    (f.comp f').charEigenspaceMap χ = f.charEigenspaceMap χ ∘ₗ f'.charEigenspaceMap χ :=
  (rfl)

/-- Taking `χ`-eigensubmodules preserves injectivity. -/
theorem charEigenspaceMap_injective {f : IntertwiningMap ρ σ} (hf : Function.Injective f) :
    Function.Injective (f.charEigenspaceMap χ) := fun _ _ h =>
  Subtype.ext <| hf <| congrArg Subtype.val h

end IntertwiningMap

end Monoid

section Group

variable [Group G] (ρ : Representation k G V) (χ : G →* kˣ)

/-- **The `χ`-eigensubmodule is the invariants of the twist by `χ⁻¹`.** -/
theorem charEigenspace_eq_invariants_charTwist :
    ρ.charEigenspace χ = (charTwist χ⁻¹ ρ).invariants := by
  ext v
  simp only [mem_charEigenspace_iff_inv_smul, mem_invariants, charTwist_apply_apply,
    MonoidHom.inv_apply]

/-- The eigensubmodule of the trivial character is the space of invariants. -/
@[simp]
theorem charEigenspace_one : ρ.charEigenspace 1 = ρ.invariants := by
  ext v
  simp [mem_invariants]

end Group

section Finite

variable [Group G] [Fintype G] (ρ : Representation k G V) {σ : Representation k G W}
  {τ : Representation k G U} (χ : G →* kˣ)

/-- **The character sum** `S_χ(v) = ∑ g, χ(g)⁻¹ ρ(g) v` of a linear character `χ` of a finite
group. It is unnormalised: no invertibility of `#G` is needed. It is defined as the group sum
`Representation.norm` of the twist `Representation.charTwist χ⁻¹ ρ`;
`Representation.charSum_apply` expands it. -/
noncomputable def charSum : Module.End k V :=
  (charTwist χ⁻¹ ρ).norm

/-- The character sum is the `χ⁻¹`-weighted sum of the operators `ρ g`. -/
theorem charSum_eq_sum : ρ.charSum χ = ∑ g, (((χ g)⁻¹ : kˣ) : k) • ρ g := by
  simp [charSum, Representation.norm]

/-- The character sum of `v` is the `χ⁻¹`-weighted sum of the vectors `ρ g v`. -/
theorem charSum_apply (v : V) : ρ.charSum χ v = ∑ g, (((χ g)⁻¹ : kˣ) : k) • ρ g v := by
  simp [charSum_eq_sum]

/-- The character sum of the trivial character is the group sum `Representation.norm`. -/
@[simp]
theorem charSum_one : ρ.charSum 1 = ρ.norm := by
  simp [charSum_eq_sum, Representation.norm]

/-- For the trivial group the character sum is the identity. -/
theorem charSum_of_subsingleton [Subsingleton G] : ρ.charSum χ = 1 := by
  rw [charSum_eq_sum, Fintype.sum_subsingleton _ 1]
  simp

/-- **The character sum lands in the eigensubmodule**: `S_χ(v) ∈ V^χ`. -/
theorem charSum_apply_mem (v : V) : ρ.charSum χ v ∈ ρ.charEigenspace χ := by
  rw [charEigenspace_eq_invariants_charTwist, mem_invariants, charSum]
  exact fun g => self_norm_apply _ g v

/-- On the eigensubmodule the character sum is multiplication by the order of the group. -/
theorem charSum_apply_of_mem {v : V} (hv : v ∈ ρ.charEigenspace χ) :
    ρ.charSum χ v = Nat.card G • v := by
  rw [mem_charEigenspace_iff_inv_smul] at hv
  simp [charSum_apply, hv, Nat.card_eq_fintype_card]

/-- **The character sum squares to the group order times itself**: `S_χ ∘ S_χ = #G • S_χ`. -/
theorem charSum_comp_charSum : ρ.charSum χ ∘ₗ ρ.charSum χ = Nat.card G • ρ.charSum χ :=
  LinearMap.ext fun v => ρ.charSum_apply_of_mem χ (ρ.charSum_apply_mem χ v)

/-- **The translation law**: `S_χ(ρ(g) v) = χ(g) S_χ(v)`. -/
@[simp]
theorem charSum_self_apply (g : G) (v : V) :
    ρ.charSum χ (ρ g v) = (χ g : k) • ρ.charSum χ v := by
  have h := norm_self_apply (charTwist χ⁻¹ ρ) g v
  rw [charTwist_apply_apply, map_smul, MonoidHom.inv_apply] at h
  rw [charSum, ← h, ← Units.smul_def, ← Units.smul_def, smul_inv_smul]

/-- The translation law as an identity of operators: `S_χ ∘ ρ(g) = χ(g) S_χ`. -/
@[simp]
theorem charSum_comp_self (g : G) : ρ.charSum χ ∘ₗ ρ g = (χ g : k) • ρ.charSum χ :=
  LinearMap.ext fun v => ρ.charSum_self_apply χ g v

/-- **The Euler-factor identity**: `S_χ(u - ρ(φ⁻¹) u) = (1 - χ(φ)⁻¹) S_χ(u)`. For `φ` a Frobenius,
this turns the Euler factor `1 - Fr⁻¹` into the scalar `1 - χ(Fr)⁻¹`. -/
theorem charSum_sub_self_inv_apply (φ : G) (u : V) :
    ρ.charSum χ (u - ρ φ⁻¹ u) = (1 - (((χ φ)⁻¹ : kˣ) : k)) • ρ.charSum χ u := by
  rw [map_sub, charSum_self_apply, map_inv, sub_smul, one_smul]

/-- **Intertwining maps commute with character sums**: `f(S_χ v) = S_χ(f v)`. -/
theorem IntertwiningMap.map_charSum (f : IntertwiningMap ρ σ) (v : V) :
    f (ρ.charSum χ v) = σ.charSum χ (f v) := by
  simp only [charSum_apply, map_sum, map_smul, f.isIntertwining]

/-- **The character sum maps onto the eigensubmodule** when the order of the group is a unit: this
is `Representation.range_norm_eq_invariants` for the twist of `ρ` by `χ⁻¹`. -/
theorem range_charSum (hG : IsUnit (Nat.card G : k)) :
    LinearMap.range (ρ.charSum χ) = ρ.charEigenspace χ := by
  rw [Nat.card_eq_fintype_card] at hG
  let := hG.invertible
  rw [charSum, range_norm_eq_invariants, charEigenspace_eq_invariants_charTwist]

end Finite

section Exact

variable [Group G] [Finite G] {ρ : Representation k G V} {σ : Representation k G W}
  {τ : Representation k G U} (χ : G →* kˣ)

namespace IntertwiningMap

/-- A preimage under `f` of a vector of `W^χ` can be chosen in `V^χ`, when `#G` is a unit. -/
private theorem exists_mem_charEigenspace_apply_eq (hG : IsUnit (Nat.card G : k))
    (f : IntertwiningMap ρ σ) {v : V} (hv : f v ∈ σ.charEigenspace χ) :
    ∃ v' ∈ ρ.charEigenspace χ, f v' = f v := by
  have : Fintype G := Fintype.ofFinite G
  refine ⟨((hG.unit⁻¹ : kˣ) : k) • ρ.charSum χ v,
    Submodule.smul_mem _ _ (ρ.charSum_apply_mem χ v), ?_⟩
  rw [map_smul, map_charSum, charSum_apply_of_mem _ _ hv, ← Nat.cast_smul_eq_nsmul k, smul_smul,
    IsUnit.val_inv_mul, one_smul]

/-- **Taking eigensubmodules preserves surjections** when the order of the group is a unit. -/
theorem charEigenspaceMap_surjective (hG : IsUnit (Nat.card G : k))
    {f : IntertwiningMap ρ σ} (hf : Function.Surjective f) :
    Function.Surjective (f.charEigenspaceMap χ) := by
  rintro ⟨w, hw⟩
  obtain ⟨v, rfl⟩ := hf w
  obtain ⟨v', hv', hfv'⟩ := exists_mem_charEigenspace_apply_eq χ hG f hw
  exact ⟨⟨v', hv'⟩, Subtype.ext hfv'⟩

/-- **Taking eigensubmodules is exact** when the order of the group is a unit: an exact sequence
`V → W → U` of representations gives an exact sequence `V^χ → W^χ → U^χ`. -/
theorem exact_charEigenspaceMap (hG : IsUnit (Nat.card G : k)) {f : IntertwiningMap ρ σ}
    {f' : IntertwiningMap σ τ} (h : Function.Exact f f') :
    Function.Exact (f.charEigenspaceMap χ) (f'.charEigenspaceMap χ) := by
  rintro ⟨w, hw⟩
  constructor
  · intro hw0
    obtain ⟨v, rfl⟩ := (h w).1 (congrArg Subtype.val hw0)
    obtain ⟨v', hv', hfv'⟩ := exists_mem_charEigenspace_apply_eq χ hG f hw
    exact ⟨⟨v', hv'⟩, Subtype.ext hfv'⟩
  · rintro ⟨v, hv⟩
    rw [← hv]
    exact Subtype.ext <| (h _).2 ⟨v, rfl⟩

end IntertwiningMap

end Exact

end Representation
