/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.DiamondOperators
public import TauCeti.NumberTheory.ModularForms.Newforms.Descent.Cusps

/-!
# The descent of a cusp form to the lower level

For a prime `p ∣ N` and `f ∈ S_k(Γ₁(N), χ)` whose nebentypus `χ` is the pull-back of a character
`χ₀` modulo `N / p`, the descent slash sum `descendSlash k p N f` (`Newforms/Descent/Sum.lean`) is
a cusp form of level `Γ₁(N / p)`, in the space of `χ₀`: it is `Γ₀(N / p)`-equivariant with
nebentypus `χ₀` (`descendSlash_slash_mapGL_of_nebentypus_of_prime`), holomorphic as a sum of
slashes of `f`, and vanishes at the cusps (`Newforms/Descent/Cusps.lean`). This is the operator
`f ↦ ∑_v f ∣[k] descendMatrix p N v` of Miyake's Lemma 4.6.14, bundled.

## Main definitions

* `TauCeti.descendCuspForm`: the descent of `f` as a cusp form of level `Γ₁(N / p)`.

## Main results

* `TauCeti.coe_descendCuspForm`: its underlying function is `descendSlash k p N f`.
* `TauCeti.descendCuspForm_mem_cuspFormCharSpace`: it lies in `S_k(Γ₁(N / p), χ₀)`.

## Provenance

Adapted from the AINTLIB `LeanModularForms` project (Chris Birkbeck, Apache-2.0,
<https://github.com/CBirkbeck/AINTLIB> @ `eb9621e7bcb0ce220ad53983ec45d987cb5b9002`),
`projects/LeanModularForms/LeanModularForms/StrongMultiplicityOne/DescentCharSpace.lean`,
`descendSlashSumCuspForm` and `descendSlashSumCuspForm_mem_charSpace`.

## References

* [T. Miyake, *Modular forms*][miyake1989], Lemma 4.6.14.
-/

public section

open Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup

open scoped Manifold MatrixGroups ModularForm

namespace TauCeti

variable {p N : ℕ} (k : ℤ) [NeZero N]

/-- **The descent of a cusp form.** For `p ∣ N` prime and `f ∈ S_k(Γ₁(N), χ)` with `χ` the
pull-back of `χ₀` modulo `N / p`, the descent slash sum of `f` as a cusp form of level
`Γ₁(N / p)`. -/
noncomputable def descendCuspForm (hp : p.Prime) (hpN : p ∣ N) {χ : (ZMod N)ˣ →* ℂˣ}
    {χ₀ : (ZMod (N / p))ˣ →* ℂˣ} (hcomp : χ = χ₀.comp (ZMod.unitsMap (Nat.div_dvd_of_dvd hpN)))
    {f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k} (hf : f ∈ cuspFormCharSpace k χ) :
    CuspForm ((Gamma1 (N / p)).map (mapGL ℝ)) k :=
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : NeZero (N / p) := ⟨(Nat.div_pos (Nat.le_of_dvd (NeZero.pos N) hpN) hp.pos).ne'⟩
  { toFun := descendSlash k p N f
    slash_action_eq' := fun γ hγ ↦ by
      obtain ⟨δ, hδ, rfl⟩ := Subgroup.mem_map.mp hγ
      rw [descendSlash_slash_mapGL_of_nebentypus_of_prime k hp hpN hcomp
        ⟨δ, Gamma1_in_Gamma0 (N / p) hδ⟩ ((mem_cuspFormCharSpace_iff_nebentypus k χ f).mp hf)]
      have h1 : (Gamma0Map (N / p)).toHomUnits ⟨δ, Gamma1_in_Gamma0 (N / p) hδ⟩ = 1 :=
        Units.ext (by
          rw [MonoidHom.coe_toHomUnits, Gamma0Map_apply]
          exact (mem_Gamma1_iff.mp hδ).2)
      rw [h1, map_one, Units.val_one, one_smul]
    holo' := mdifferentiable_descendSlash k p N (ModularFormClass.holo f)
    zero_at_cusps' := fun hc ↦ isZeroAt_descendSlash k
      (fun c hc ↦ f.zero_at_cusps' (Subgroup.IsArithmetic.isCusp_of_isCusp c hc)) hc }

/-- The underlying function of the descent is the descent slash sum. -/
@[simp]
lemma coe_descendCuspForm (hp : p.Prime) (hpN : p ∣ N) {χ : (ZMod N)ˣ →* ℂˣ}
    {χ₀ : (ZMod (N / p))ˣ →* ℂˣ} (hcomp : χ = χ₀.comp (ZMod.unitsMap (Nat.div_dvd_of_dvd hpN)))
    {f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k} (hf : f ∈ cuspFormCharSpace k χ) :
    haveI : NeZero p := ⟨hp.ne_zero⟩
    ⇑(descendCuspForm k hp hpN hcomp hf) = descendSlash k p N f :=
  (rfl)

/-- **The descent lowers the level of the nebentypus**: the descent of `f ∈ S_k(Γ₁(N), χ)` lies
in `S_k(Γ₁(N / p), χ₀)`. -/
theorem descendCuspForm_mem_cuspFormCharSpace (hp : p.Prime) (hpN : p ∣ N)
    {χ : (ZMod N)ˣ →* ℂˣ} {χ₀ : (ZMod (N / p))ˣ →* ℂˣ}
    (hcomp : χ = χ₀.comp (ZMod.unitsMap (Nat.div_dvd_of_dvd hpN)))
    {f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k} (hf : f ∈ cuspFormCharSpace k χ) :
    descendCuspForm k hp hpN hcomp hf ∈ cuspFormCharSpace k χ₀ := by
  have : NeZero p := ⟨hp.ne_zero⟩
  rw [mem_cuspFormCharSpace_iff_nebentypus, coe_descendCuspForm]
  intro γ
  exact descendSlash_slash_mapGL_of_nebentypus_of_prime k hp hpN hcomp γ
    ((mem_cuspFormCharSpace_iff_nebentypus k χ f).mp hf)

end TauCeti
