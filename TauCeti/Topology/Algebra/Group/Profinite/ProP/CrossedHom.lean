/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.CrossedHom
public import TauCeti.Topology.Algebra.Group.LowerCentralSeries
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.PadicUnits
import TauCeti.Topology.Algebra.Group.LowerCentralSeries.Graded.Heisenberg

/-!
# Crossed homomorphisms of pro-`p` groups into `ℤ_p`

Let `G` be a pro-`p` group, `χ : G →ₜ* ℤ_pˣ` a continuous character and `f : G → ℤ_p` a continuous
crossed homomorphism for `χ`, that is `f (g * h) = χ g * f h + f g`. Since `χ` takes values in the
principal units `1 + pℤ_p` (`TauCeti.IsProP.mem_unitsPrincipal_one`), the reduction of `f` modulo
`p` is a continuous homomorphism `G → 𝔽_p`, and such a homomorphism kills the Frattini subgroup
`λ_1(G) = Φ(G)`. So `f` vanishes modulo `p` on the Frattini subgroup.

## Main results

* `TauCeti.IsCrossedHom.dvd_apply_of_mem_pLowerCentralSeries_one`: a continuous crossed
  homomorphism of a pro-`p` group `G` vanishes modulo `p` on the Frattini subgroup `λ_1(G)`.
-/

public section

namespace TauCeti

open ContCohomology

-- Preferring the ring path keeps a single additive structure on `ZMod p`, so that the trivial
-- action installed below is the one the cocycles are stated against.
attribute [local instance 2000] Ring.toAddCommGroup

variable {p : ℕ} [Fact p.Prime] {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- **A continuous crossed homomorphism of a pro-`p` group vanishes modulo `p` on the Frattini
subgroup.** For a continuous character `χ : G → ℤ_pˣ` of a pro-`p` group `G` and a continuous
crossed homomorphism `f` for `χ`, the reduction of `f` modulo `p` is a continuous character with
values in `𝔽_p`, because `χ ≡ 1 mod p`, and such a character kills `λ_1(G) = Φ(G)`. -/
theorem IsCrossedHom.dvd_apply_of_mem_pLowerCentralSeries_one (hG : IsProP p G)
    {χ : G →ₜ* ℤ_[p]ˣ} {f : G → ℤ_[p]} (hf : IsCrossedHom χ f) (hfc : Continuous f) {g : G}
    (hg : g ∈ pLowerCentralSeries p G 1) : (p : ℤ_[p]) ∣ f g := by
  rw [← PadicInt.toZMod_eq_zero_iff_dvd]
  let _ : DistribMulAction G (ZMod p) := DistribMulAction.compHom (ZMod p) (1 : G →* (ZMod p)ˣ)
  have htriv : ∀ (g : G) (x : ZMod p), g • x = x := fun _ x ↦ one_smul (ZMod p)ˣ x
  have hχ1 : ∀ g, PadicInt.toZMod (χ g : ℤ_[p]) = 1 := fun g ↦
    mem_unitsPrincipal_one_iff_toZMod.1 (hG.mem_unitsPrincipal_one χ g)
  refine apply_eq_zero_of_mem_Z1_of_mem_pLowerCentralSeries_one htriv
    (ZModModule.char_nsmul_eq_zero p) (f := fun g ↦ PadicInt.toZMod (f g))
    (mem_Z1_iff.2 ⟨PadicInt.continuous_toZMod.comp hfc, fun g h ↦ ?_⟩) hg
  dsimp only
  rw [htriv, hf.map_mul g h, map_add, _root_.map_mul, hχ1, one_mul]

end TauCeti
