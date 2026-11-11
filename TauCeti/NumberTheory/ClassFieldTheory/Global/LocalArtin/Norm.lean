/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Global.LocalArtin.Compatibility
import TauCeti.NumberTheory.NumberField.Global.Ideles.Norm.Open

/-!
# Norm functoriality of the global Artin map in the ground field

Let `K ⊆ E ⊆ L` be number fields with `L/K` finite Galois. The global Artin maps of `L/K` and of
`L/E` are related by the idele-class norm `N_{E/K} : C_E → C_K`: for every `c ∈ C_E`,

```text
Art_{L/K} (N_{E/K} c) = Art_{L/E} c      in Gal(L/K)^ab,
```

the right side read through the map `Gal(L/E)^ab → Gal(L/K)^ab` induced by the inclusion
`Gal(L/E) ≤ Gal(L/K)` (`globalArtinMap_ideleClassNormMap`). Together with `globalArtinMap_comp`,
which changes the top field, this is the compatibility of the global Artin map in towers; it is
the global form of the norm diagram `ClassFormation.artinMap_groundNorm` of an abstract class
formation.

The proof is local. Both sides are homomorphisms `C_E → Gal(L/K)^ab` with open kernels, the
first containing the preimage of `N_{L/K}(C_L)` and the second containing `N_{L/E}(C_L)`
(`isOpen_range_ideleClassNormMap`). So both kill a ray subgroup of `C_E`
(`exists_raySubgroup_le_of_isOpen`), and they agree as soon as they agree on the ideles
concentrated at one finite place (`ideleClassGroup_hom_ext_of_raySubgroup_le`). On such an
idele, with component `y` at a place `w` of `E` above `v`, the norm is concentrated at `v` with
component `N_{E_w/K_v}(y)` (`ideleClassNormMap_ofAdicCompletion`), both global symbols are local
symbols (`globalArtinMap_local`), and the local symbols agree by `localArtinAt_norm`.

## Main results

* `TauCeti.ClassFieldTheory.globalArtinMap_ideleClassNormMap`: the global Artin symbol of the
  norm of an idele class of an intermediate field is its global Artin symbol over that field.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter IV, §6 (functoriality of the reciprocity map)
  and Chapter VI, §5 (the global norm residue symbol and its local components).
-/

public section

noncomputable section

namespace TauCeti.ClassFieldTheory

open IsDedekindDomain _root_.NumberField GlobalNumberFields

variable {K : Type} [Field K] [NumberField K] {E : Type} [Field E] [NumberField E] [Algebra K E]
  {L : Type} [Field L] [NumberField L] [Algebra K L] [Algebra E L] [IsScalarTower K E L]
  [IsGalois K L] [IsGalois E L]

/-- **Norm functoriality of the global Artin map in the ground field.** Let `K ⊆ E ⊆ L` be number
fields with `L/K` finite Galois, embedded in separable closures of `K` and of `E` by `ι` and
`ι'`. The global Artin symbol in `Gal(L/K)^ab` of the norm `N_{E/K}(c)` of an idele class
`c ∈ C_E` is the global Artin symbol of `c` in `Gal(L/E)^ab`, mapped to `Gal(L/K)^ab` by the
inclusion `Gal(L/E) ≤ Gal(L/K)`:

```text
Art_{L/K} (N_{E/K} c) = Art_{L/E} c.
```

The instance `IsGalois E L` follows from `IsGalois K L` (`IsGalois.tower_top_of_isGalois`). -/
theorem globalArtinMap_ideleClassNormMap (ι : L →ₐ[K] SeparableClosure K)
    (ι' : L →ₐ[E] SeparableClosure E) (c : IdeleClassGroup (𝓞 E) E) :
    globalArtinMap K L ι (.ofMul (ideleClassNormMap K E c)) =
      (Abelianization.map (AlgEquiv.restrictScalarsHom K)).toAdditive
        (globalArtinMap E L ι' (.ofMul c)) := by
  -- The two sides, as homomorphisms `C_E →* Gal(L/K)^ab`.
  let F : IdeleClassGroup (𝓞 E) E →* Abelianization Gal(L/K) :=
    (MonoidHom.toAdditive.symm (globalArtinMap K L ι)).comp
      (ideleClassNormMap K E : IdeleClassGroup (𝓞 E) E →* IdeleClassGroup (𝓞 K) K)
  let G : IdeleClassGroup (𝓞 E) E →* Abelianization Gal(L/K) :=
    (Abelianization.map (AlgEquiv.restrictScalarsHom K)).comp
      (MonoidHom.toAdditive.symm (globalArtinMap E L ι'))
  -- Their kernels contain the open norm groups, so both kill some ray subgroup of `C_E`.
  have hF : IsOpen (F.ker : Set (IdeleClassGroup (𝓞 E) E)) := by
    have : F.ker = (ideleClassNormMap K L :
        IdeleClassGroup (𝓞 L) L →* IdeleClassGroup (𝓞 K) K).range.comap
          (ideleClassNormMap K E : IdeleClassGroup (𝓞 E) E →* IdeleClassGroup (𝓞 K) K) := by
      ext c
      rw [MonoidHom.mem_ker, Subgroup.mem_comap, ← globalArtinMap_eq_zero_iff K L ι]
      exact toMul_eq_one
    rw [this, Subgroup.coe_comap]
    exact (isOpen_range_ideleClassNormMap K L).preimage (continuous_ideleClassNormMap K E)
  have hG : IsOpen (G.ker : Set (IdeleClassGroup (𝓞 E) E)) := by
    refine Subgroup.isOpen_mono (fun c hc ↦ ?_) (isOpen_range_ideleClassNormMap E L)
    have h0 := (globalArtinMap_eq_zero_iff E L ι' c).mpr hc
    rw [MonoidHom.mem_ker]
    simp [G, h0]
  obtain ⟨𝔪, h𝔪⟩ := exists_raySubgroup_le_of_isOpen (F.ker ⊓ G.ker) (by
    rw [Subgroup.coe_inf]
    exact hF.inter hG)
  -- On an idele concentrated at a finite place `w`, both sides are local Artin symbols.
  have hFG : F = G := ideleClassGroup_hom_ext_of_raySubgroup_le (h𝔪.trans inf_le_left)
    (h𝔪.trans inf_le_right) fun w _ y _ ↦ by
      simp only [F, G, MonoidHom.comp_apply, MonoidHom.coe_ofClass,
        MonoidHom.toAdditive_symm_apply_apply]
      rw [ideleClassNormMap_ofAdicCompletion (w.under (𝓞 K)) w,
        IdeleClassGroup.ofAdicCompletion_apply, IdeleClassGroup.ofAdicCompletion_apply,
        globalArtinMap_local, globalArtinMap_local, toMul_ofMul, toMul_ofMul,
        localArtinAt_norm]
  exact congrArg Additive.ofMul (DFunLike.congr_fun hFG c)

end TauCeti.ClassFieldTheory
