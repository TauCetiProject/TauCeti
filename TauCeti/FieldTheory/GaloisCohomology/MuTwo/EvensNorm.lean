/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.GaloisCohomology.EvensNorm
public import TauCeti.FieldTheory.GaloisCohomology.MuTwo.KummerCharacter
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.TrivialF2.Inhomogeneous
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Evens.DihedralPullback

/-!
# The Evens norm of a mod-two Kummer class as a pullback of the `D₁₆` class

Let `L/K` be a quadratic extension, `σ : L →ₐ[K] Kˢ` a `K`-embedding, and write
`G_L = galoisSubgroup K L σ`, an open subgroup of index two in `G_K`. For `a ∈ Lˣ` choose a square
root `r ∈ Kˢ` of `σ a` and an element `s ∈ G_K ∖ G_L`. The Kummer class `(a) ∈ H¹(G_L, 𝔽₂)` is the
class of the Kummer character `α_a : γ ↦ rootSign r γ` of `G_L`
(`TauCeti.galoisF2Iso_inv_kummerClass`), and its induced homomorphism

```text
ρ_a = Ind α_a : G_K → C₂ ≀ C₂
```

at `s` is `TauCeti.kummerInd`. Read through the signed-permutation representation of `C₂ ≀ C₂`,
`ρ_a` is the action of `G_K` on the roots `r, s r` of `X² − σ a` and `X² − s (σ a)`; that reading
is not formalised here.

Since the index-two Evens norm of the class of a continuous homomorphism is the pullback of the
`D₁₆` extension class `c_{D₁₆}` along its induced homomorphism
(`TauCeti.ContCohomology.evensNormIndexTwo_eq_ind_pullback`), the Evens norm of the Kummer class is
the class of the explicit `2`-cocycle `c_{D₁₆} ∘ (ρ_a × ρ_a)` of `G_K`:

```text
N^{Ev}((a)) = ρ_a^* c_{D₁₆}
```

(`TauCeti.galoisEvens_kummerClass_eq_pullback`). This is the first step of Serre's computation of
`N^{Ev}((a))` in terms of Kummer classes of `K`, which evaluates `c_{D₁₆} ∘ (ρ_a × ρ_a)` through a
lift of `ρ_a` to the dihedral group of order sixteen in `Pin⁺₂`.

## Main definitions

* `TauCeti.kummerInd`: the induced homomorphism `ρ_a = Ind α_a : G_K → C₂ ≀ C₂` of the Kummer
  character of `a ∈ Lˣ` on `G_L`.

## Main results

* `TauCeti.galoisEvens_kummerClass_eq_pullback`: `N^{Ev}((a))` is the class of
  `c_{D₁₆} ∘ (ρ_a × ρ_a)`.

## References

* J.-P. Serre, *L'invariant de Witt de la forme Tr(x²)*, Comment. Math. Helv. **59** (1984),
  651–676, §2.
* B. Kahn, *Classes de Stiefel-Whitney de formes quadratiques et de représentations galoisiennes
  réelles*, Invent. Math. **78** (1984), 223–256, Lemme II.2.1.
-/

public section

noncomputable section

namespace TauCeti

open ContCohomology

universe u

variable {K : Type u} [Field K] {L : Type u} [Field L] [Algebra K L] [FiniteDimensional K L]

/-- **The representation `ρ_a = Ind α_a : G_K → C₂ ≀ C₂`** of `a ∈ Lˣ` for a quadratic extension
`L/K`: the induced homomorphism `indexTwoInd`, at an element `s ∉ G_L`, of the Kummer character
`α_a = galoisKummerCharacter σ a r hr` of `G_L = galoisSubgroup K L σ`, for a square root `r` of
`σ a`. Read through the signed-permutation representation of `C₂ ≀ C₂`, it is the action of `G_K`
on the roots `r, s r` of `X² − σ a` and `X² − s (σ a)`. -/
def kummerInd (σ : L →ₐ[K] SeparableClosure K) (hdeg : Module.finrank K L = 2) (a : Lˣ)
    (r : SeparableClosure K) (hr : r ^ 2 = σ (a : L)) (s : AbsoluteGaloisGroup K)
    (hs : s ∉ galoisSubgroup K L σ) : AbsoluteGaloisGroup K →* WreathC2 :=
  indexTwoInd (galoisSubgroup K L σ).toSubgroup ((galoisSubgroup_index K L σ).trans hdeg) s hs
    (galoisKummerCharacter σ a r hr)

/-- `kummerInd` is the induced homomorphism of the Kummer character on `galoisSubgroup K L σ`. -/
theorem kummerInd_def (σ : L →ₐ[K] SeparableClosure K) (hdeg : Module.finrank K L = 2) (a : Lˣ)
    (r : SeparableClosure K) (hr : r ^ 2 = σ (a : L)) (s : AbsoluteGaloisGroup K)
    (hs : s ∉ galoisSubgroup K L σ) :
    kummerInd σ hdeg a r hr s hs =
      indexTwoInd (galoisSubgroup K L σ).toSubgroup ((galoisSubgroup_index K L σ).trans hdeg) s hs
        (galoisKummerCharacter σ a r hr) :=
  (rfl)

/-- The pullback `c_{D₁₆} ∘ (ρ_a × ρ_a)` of the `D₁₆` extension cocycle along `kummerInd` is
continuous: `ρ_a` is locally constant, because `galoisSubgroup K L σ` is open and the Kummer
character is continuous. -/
theorem continuous_wreathD16Cocycle_kummerInd (σ : L →ₐ[K] SeparableClosure K)
    (hdeg : Module.finrank K L = 2) (a : Lˣ) (r : SeparableClosure K) (hr : r ^ 2 = σ (a : L))
    (s : AbsoluteGaloisGroup K) (hs : s ∉ galoisSubgroup K L σ) :
    Continuous fun q : AbsoluteGaloisGroup K × AbsoluteGaloisGroup K =>
      wreathD16Cocycle (kummerInd σ hdeg a r hr s hs q.1, kummerInd σ hdeg a r hr s hs q.2) := by
  rw [kummerInd_def]
  exact continuous_wreathD16Cocycle_indexTwoInd _ _ s hs _ (galoisSubgroup K L σ).isOpen'
    (continuous_galoisKummerCharacter σ a r hr)

/-- **The Evens norm of a Kummer class is the pullback of the `D₁₆` class:** for a quadratic
extension `L/K`, `a ∈ Lˣ`, a square root `r` of `σ a` and any `s ∉ galoisSubgroup K L σ`,
`N^{Ev}((a)) ∈ H²(G_K, 𝔽₂)` is the class of the `2`-cocycle `c_{D₁₆} ∘ (ρ_a × ρ_a)`, where
`ρ_a = kummerInd σ hdeg a r hr s hs` and `c_{D₁₆} = wreathD16Cocycle`. -/
theorem galoisEvens_kummerClass_eq_pullback [Invertible (2 : L)]
    (σ : L →ₐ[K] SeparableClosure K) (hdeg : Module.finrank K L = 2) (a : Lˣ)
    (r : SeparableClosure K) (hr : r ^ 2 = σ (a : L)) (s : AbsoluteGaloisGroup K)
    (hs : s ∉ galoisSubgroup K L σ) :
    galoisEvens K L σ hdeg (kummerClass a) =
      f2CocycleClass
        (fun q => wreathD16Cocycle (kummerInd σ hdeg a r hr s hs q.1,
          kummerInd σ hdeg a r hr s hs q.2))
        (continuous_wreathD16Cocycle_kummerInd σ hdeg a r hr s hs)
        (fun g h j => by simp only [map_mul]; exact wreathD16Cocycle_isCocycle _ _ _) := by
  rw [galoisEvens_def, galoisF2Iso_inv_kummerClass σ a r hr,
    evensNormIndexTwo_eq_ind_pullback _ _ s hs, f2CocycleClass_def]
  simp only [kummerInd_def]

end TauCeti
