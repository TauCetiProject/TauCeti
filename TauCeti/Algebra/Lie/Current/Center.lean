/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Current.Completion
public import TauCeti.Topology.Algebra.Algebra.Center

/-!
# The center of the completed enveloping algebra at a fixed level

Let `Û = lim_N U / I_N` be the completed enveloping algebra of the residue central extension
`ĝ = L((t)) ⊕ R K` of an invariant symmetric form `Φ` at the central value `a`
(`TauCeti.CurrentAlgebra.CompletedEnveloping`). Its center is Mathlib's `Subalgebra.center R Û`.
This file develops the properties of this completed center which precede any center theorem.

* **Closedness and completeness.** Since `Û` is a Hausdorff topological ring, its center is closed
  (`Subalgebra.isClosed_center`), and complete since `Û` is.
* **Its topology.** The elements of the center whose image in `U / I_n` vanishes form an ideal
  `Z ∩ ker π_n` of the commutative center (`TauCeti.CurrentAlgebra.centerOrderIdeal`), although
  `ker π_n` is only a left ideal of `Û`: a central element times an element of `ker π_n` lies in
  `ker π_n`. These ideals decrease and form a basis of neighbourhoods of zero for the subspace
  topology, so the center is a complete commutative ring with a linear topology.
* **Centrality is detected on the current generators.** The images of the currents `u ∈ L((t))`
  topologically generate `Û`, since they generate `U` as an algebra and the image of `U` is dense
  (`TauCeti.CurrentAlgebra.topologicalClosure_adjoin_range_envelopingι`). Hence an element of `Û`
  is central as soon as it commutes with the images of all currents
  (`TauCeti.CurrentAlgebra.mem_center_iff_forall_commute`).
* **The action on smooth modules.** On a module `M` over `U` which is smooth for the left ideals
  `I_n`, every point of `Û` acts by the extension `TauCeti.ModuleTower.limSmul` of the action of
  `U`. A central element acts by an endomorphism of `U`-modules which commutes with the action of
  all of `Û`. This gives a ring homomorphism from the center to the `U`-linear endomorphisms of
  `M` (`TauCeti.CurrentAlgebra.centerToModuleEnd`), natural in `M`.

At `a = 1` and `Φ = -κ` this is the center `Z(Û_κ)` of the completed enveloping algebra at level
`κ`.

## Main definitions

* `TauCeti.CurrentAlgebra.centerOrderIdeal`: the ideal `Z ∩ ker (Û → U / I_n)` of the center.
* `TauCeti.CurrentAlgebra.centerToModuleEnd`: the action of the center on a smooth module.

## Main results

* `TauCeti.CurrentAlgebra.hasBasis_nhds_zero_center`: the ideals `Z ∩ ker π_n` form a basis of
  neighbourhoods of zero in the center.
* `TauCeti.CurrentAlgebra.topologicalClosure_adjoin_range_envelopingι`: the images of the currents
  topologically generate `Û`.
* `TauCeti.CurrentAlgebra.mem_center_iff_forall_commute`: centrality is detected on the current
  generators.
* `TauCeti.CurrentAlgebra.limSmul_smul_of_mem_center`,
  `TauCeti.CurrentAlgebra.limSmul_centerToModuleEnd`: central elements act on smooth modules by
  `U`-linear endomorphisms commuting with the action of `Û`.

## References

* E. Frenkel, *Langlands Correspondence for Loop Groups*, §3.2.1 and §4.3, for the center
  `Z(Û_κ)` of the completed enveloping algebra and its action on smooth modules.
-/

public section

noncomputable section

open TauCeti.UniversalEnvelopingAlgebra Topology

namespace TauCeti.CurrentAlgebra

universe v

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  (Φ : LinearMap.BilinForm R L) (hΦ : Φ.lieInvariant L) (hΦs : Φ.IsSymm) (a : R)

local notation "UK" => CentralQuotient R (centralElement Φ hΦ hΦs) a
local notation "Û" => CompletedEnveloping Φ hΦ hΦs a

/-! ### The topology of the center -/

/-- **The ideal `Z ∩ ker (Û → U / I_n)` of the completed center**: the central elements whose image
in `U / I_n` vanishes. It is an ideal of the commutative center, although the kernel of the
projection is only a left ideal of `Û`. -/
def centerOrderIdeal (n : ℕ) : Ideal (Subalgebra.center R Û) where
  carrier := {z | (z : Û) ∈ completedOrderLeftIdeal Φ hΦ hΦs a n}
  add_mem' := add_mem
  zero_mem' := zero_mem _
  smul_mem' w _ hz := (completedOrderLeftIdeal Φ hΦ hΦs a n).smul_mem (w : Û) hz

variable {Φ hΦ hΦs a} in
@[simp]
theorem mem_centerOrderIdeal {n : ℕ} {z : Subalgebra.center R Û} :
    z ∈ centerOrderIdeal Φ hΦ hΦs a n ↔ (orderQuotientTower Φ hΦ hΦs a).limπ n z = 0 :=
  mem_completedOrderLeftIdeal

/-- The ideals `Z ∩ ker (Û → U / I_n)` decrease as `n` grows. -/
theorem centerOrderIdeal_antitone : Antitone (centerOrderIdeal Φ hΦ hΦs a) :=
  fun _ _ h _ hz ↦ mem_centerOrderIdeal.2 <| LinearMap.mem_ker.1 <|
    (orderQuotientTower Φ hΦ hΦs a).ker_limπ_antitone h <|
      LinearMap.mem_ker.2 (mem_centerOrderIdeal.1 hz)

/-- The ideals `Z ∩ ker (Û → U / I_n)` form a basis of neighbourhoods of zero in the completed
center. -/
theorem hasBasis_nhds_zero_center :
    (𝓝 (0 : Subalgebra.center R Û)).HasBasis (fun _ : ℕ ↦ True)
      fun n ↦ (centerOrderIdeal Φ hΦ hΦs a n : Set (Subalgebra.center R Û)) := by
  rw [nhds_subtype, ZeroMemClass.coe_zero]
  exact (hasBasis_nhds_zero_completedOrderLeftIdeal Φ hΦ hΦs a).comap _

/-- The topology of the completed center is linear for the ideals `Z ∩ ker (Û → U / I_n)`. -/
instance : IsLinearTopology (Subalgebra.center R Û) (Subalgebra.center R Û) :=
  .mk_of_hasBasis _ (hasBasis_nhds_zero_center Φ hΦ hΦs a)

/-! ### Centrality on generators -/

/-- **The current generators topologically generate the completed enveloping algebra**: the
closure of the subalgebra generated by the images of the currents is all of `Û`. -/
theorem topologicalClosure_adjoin_range_envelopingι :
    (Algebra.adjoin R (Set.range
      (toCompletedEnveloping Φ hΦ hΦs a ∘ envelopingι Φ hΦ hΦs a))).topologicalClosure = ⊤ := by
  rw [Set.range_comp, ← AlgHom.map_adjoin, adjoin_range_envelopingι, Algebra.map_top,
    eq_top_iff, ← SetLike.coe_subset_coe, Subalgebra.topologicalClosure_coe, AlgHom.coe_range,
    coe_toCompletedEnveloping, (ModuleTower.denseRange_toLimQuotients _ _).closure_range]
  exact Set.subset_univ _

variable {Φ hΦ hΦs a}

/-- **Centrality in the completed enveloping algebra is detected on the current generators**: an
element of `Û` is central exactly when it commutes with the images of all currents. -/
theorem mem_center_iff_forall_commute {z : Û} :
    z ∈ Subalgebra.center R Û ↔
      ∀ u, Commute (toCompletedEnveloping Φ hΦ hΦs a (envelopingι Φ hΦ hΦs a u)) z := by
  rw [Subalgebra.mem_center_iff_forall_commute_of_topologicalClosure_adjoin_eq_top
    (topologicalClosure_adjoin_range_envelopingι Φ hΦ hΦs a), Set.forall_mem_range]
  simp only [Function.comp_apply]

/-! ### The action on smooth modules -/

section Action

variable {M N : ModuleCat.{v} (CentralQuotient R (centralElement Φ hΦ hΦs) a)}
  (hM : smoothModules (fun n : ℕ ↦ orderLeftIdeal Φ hΦ hΦs a n) M)
  (hN : smoothModules (fun n : ℕ ↦ orderLeftIdeal Φ hΦ hΦs a n) N)

/-- **Central elements of `Û` act on smooth modules by `U`-linear maps.** -/
theorem limSmul_smul_of_mem_center {z : Û} (hz : z ∈ Subalgebra.center R Û) (b : UK) (m : M) :
    ModuleTower.limSmul hM z (b • m) = b • ModuleTower.limSmul hM z m := by
  -- `b` acts as its image in `Û`, which commutes with `z`.
  have hb (m' : M) : b • m' = ModuleTower.limSmul hM (toCompletedEnveloping Φ hΦ hΦs a b) m' := by
    rw [coe_toCompletedEnveloping, ModuleTower.limSmul_toLimQuotients]
  rw [hb, hb, ← limSmul_mul, ← limSmul_mul, Subalgebra.mem_center_iff.1 hz]

/-- **The action of the completed center on a smooth module.** A central element of `Û` acts on a
module over `U` which is smooth for the left ideals `I_n` by an endomorphism of `U`-modules. -/
def centerToModuleEnd : Subalgebra.center R Û →+* Module.End UK M where
  toFun z :=
    { toFun := ModuleTower.limSmul hM z
      map_add' := ModuleTower.limSmul_add hM z
      map_smul' := limSmul_smul_of_mem_center hM z.2 }
  map_one' := LinearMap.ext fun m ↦ (ModuleTower.limSmul_toLimQuotients hM 1 m).trans (one_smul _ m)
  map_mul' z w := LinearMap.ext fun m ↦ limSmul_mul hM z w m
  map_zero' := LinearMap.ext fun m ↦ ModuleTower.zero_limSmul hM m
  map_add' z w := LinearMap.ext fun m ↦ ModuleTower.add_limSmul hM z w m

@[simp]
theorem centerToModuleEnd_apply (z : Subalgebra.center R Û) (m : M) :
    centerToModuleEnd hM z m = ModuleTower.limSmul hM z m :=
  (rfl)

/-- **Central elements act by endomorphisms commuting with the action of `Û`.** -/
theorem limSmul_centerToModuleEnd (x : Û) (z : Subalgebra.center R Û) (m : M) :
    ModuleTower.limSmul hM x (centerToModuleEnd hM z m) =
      centerToModuleEnd hM z (ModuleTower.limSmul hM x m) := by
  rw [centerToModuleEnd_apply, centerToModuleEnd_apply, ← limSmul_mul, ← limSmul_mul,
    Subalgebra.mem_center_iff.1 z.2 x]

/-- The action of the completed center is natural: linear maps between smooth modules commute
with it. -/
theorem map_centerToModuleEnd (f : M →ₗ[UK] N) (z : Subalgebra.center R Û) (m : M) :
    f (centerToModuleEnd hM z m) = centerToModuleEnd hN z (f m) :=
  ModuleTower.map_limSmul hM hN f z m

end Action

end TauCeti.CurrentAlgebra
