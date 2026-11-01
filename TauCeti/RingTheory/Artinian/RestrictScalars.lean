/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Artinian.Ring
public import Mathlib.RingTheory.Ideal.Quotient.Defs

/-!
# Artinian modules under restriction of scalars to a subring of the residue ring

Restricting scalars along a ring map `S → B` usually destroys the Artinian property: `ℚ` is an
Artinian `ℚ`-module but not an Artinian `ℤ`-module. It survives when `S → B` is surjective
(`isArtinian_of_surjective_algebraMap`), and more generally when `S` only surjects onto `B ⧸ I`
for an ideal `I` killing the module: then every `S`-submodule is a `B`-submodule.

For a finite module over an Artinian ring and a nilpotent ideal `I`, filtering by the submodules
`I ^ j • M` reduces to that case. So a finite module over an Artinian local ring `B` stays Artinian
over every ring `S` mapping onto the residue field of `B`. This is the input for fibre products of
Artinian local rings with a common residue field: such a fibre product is a subring of a product
of Artinian rings onto whose residue field it maps, hence is Artinian.

## Main results

* `TauCeti.isArtinian_of_surjective_algebraMap_quotient`: if `I` kills the Artinian `B`-module `M`
  and `S → B ⧸ I` is surjective, then `M` is an Artinian `S`-module.
* `TauCeti.isArtinian_of_isNilpotent_of_surjective_algebraMap_quotient`: if `B` is an Artinian
  ring, `M` is a finite `B`-module, `I` is nilpotent and `S → B ⧸ I` is surjective, then `M` is an
  Artinian `S`-module.
-/

public section

namespace TauCeti

variable {S B M : Type*} [CommRing S] [CommRing B] [Algebra S B] [AddCommGroup M] [Module B M]
  [Module S M] [IsScalarTower S B M]

/-- If an ideal `I` of `B` kills an Artinian `B`-module `M` and `S → B ⧸ I` is surjective, then `M`
is an Artinian `S`-module: every `S`-submodule of `M` is a `B`-submodule. -/
theorem isArtinian_of_surjective_algebraMap_quotient {I : Ideal B}
    (hI : Function.Surjective ((Ideal.Quotient.mk I).comp (algebraMap S B)))
    (hM : I ≤ Module.annihilator B M) [IsArtinian B M] : IsArtinian S M := by
  apply (OrderEmbedding.wellFoundedLT (β := Submodule B M))
  refine ⟨⟨fun N ↦ ⟨N.toAddSubmonoid, fun b x hx ↦ ?_⟩, fun N₁ N₂ h ↦ ?_⟩, .rfl⟩
  · obtain ⟨s, hs⟩ := hI (Ideal.Quotient.mk I b)
    have hbs : b • x = s • x := by
      rw [← algebraMap_smul B s x, ← sub_eq_zero, ← sub_smul]
      exact Module.mem_annihilator.mp (hM (Ideal.Quotient.eq.mp hs.symm)) x
    rw [hbs]
    exact N.smul_mem s hx
  · rw [Submodule.ext_iff] at h ⊢
    exact h

/-- One step of the `I`-adic filtration: if `N' ≤ N` are `B`-submodules with `I • N ≤ N'`, and `N'`
is an Artinian `S`-module, then so is `N`. -/
private theorem isArtinian_of_le_of_smul_le [IsArtinianRing B] [Module.Finite B M] {I : Ideal B}
    (hI : Function.Surjective ((Ideal.Quotient.mk I).comp (algebraMap S B)))
    {N' N : Submodule B M} (hle : N' ≤ N) (hIN : I • N ≤ N') [IsArtinian S N'] :
    IsArtinian S N := by
  set Q : Submodule B N := N'.comap N.subtype
  have hQ : I ≤ Module.annihilator B (N ⧸ Q) := fun a ha ↦ Module.mem_annihilator.mpr fun y ↦ by
    obtain ⟨x, rfl⟩ := Q.mkQ_surjective y
    rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact hIN (Submodule.smul_mem_smul ha x.2)
  have := isArtinian_of_surjective_algebraMap_quotient (S := S) hI hQ
  refine isArtinian_of_range_eq_ker ((Submodule.inclusion hle).restrictScalars S)
    (Q.mkQ.restrictScalars S) ?_
  rw [LinearMap.range_restrictScalars, LinearMap.ker_restrictScalars, Submodule.range_inclusion,
    Submodule.ker_mkQ]

/-- If `B` is an Artinian ring, `I` a nilpotent ideal of `B` and `S → B ⧸ I` surjective, then every
finite `B`-module is an Artinian `S`-module. In particular a finite module over an Artinian local
ring is Artinian over every ring mapping onto the residue field. -/
theorem isArtinian_of_isNilpotent_of_surjective_algebraMap_quotient [IsArtinianRing B]
    [Module.Finite B M] {I : Ideal B} (hnil : IsNilpotent I)
    (hI : Function.Surjective ((Ideal.Quotient.mk I).comp (algebraMap S B))) :
    IsArtinian S M := by
  obtain ⟨n, hn⟩ := hnil
  -- Descending induction along the filtration `I ^ j • M`, which vanishes for `j ≥ n`.
  have key (i : ℕ) : ∀ j, n ≤ j + i → IsArtinian S ↥(I ^ j • (⊤ : Submodule B M)) := by
    induction i with
    | zero =>
      intro j hj
      have : I ^ j = ⊥ := by
        rw [show j = n + (j - n) by omega, pow_add, hn, Ideal.zero_eq_bot, Ideal.bot_mul]
      rw [this, Submodule.bot_smul]
      infer_instance
    | succ i ih =>
      intro j hj
      have := ih (j + 1) (by omega)
      refine isArtinian_of_le_of_smul_le hI
        (Submodule.smul_mono_left (Ideal.pow_le_pow_right j.le_succ)) ?_
      rw [← Submodule.mul_smul, ← pow_succ']
  have := key n 0 (by simp)
  rw [pow_zero, Ideal.one_eq_top, Submodule.top_smul] at this
  exact isArtinian_of_linearEquiv
    ((Submodule.topEquiv : (⊤ : Submodule B M) ≃ₗ[B] M).restrictScalars S)

end TauCeti
