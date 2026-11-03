/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Current.Completion
public import TauCeti.Topology.Algebra.Algebra.Center
public import TauCeti.Topology.Algebra.LinearTopology

/-!
# The center of the completed enveloping algebra at a fixed level

Let `Û = lim_N U / I_N` be the completed enveloping algebra of the residue central extension
`ĝ = L((t)) ⊕ R K` of an invariant symmetric form `Φ` at the central value `a`
(`TauCeti.CurrentAlgebra.CompletedEnveloping`). Its center is Mathlib's `Subalgebra.center R Û`.
This file develops the properties of this completed center which precede any center theorem.

* **Closedness and completeness.** Since `Û` is a Hausdorff topological ring, its center is closed
  (`Subalgebra.isClosed_center`), and complete since `Û` is.
* **Its topology.** The elements of the center whose image in `U / I_n` vanishes form an ideal
  `Z ∩ ker π_n` of the commutative center (`TauCeti.CurrentAlgebra.centerOrderIdeal`), the
  preimage of the left ideal `ker π_n` of `Û`. These ideals decrease and form a basis of
  neighbourhoods of zero for the subspace topology, so the center is a complete commutative ring
  with a linear topology (`IsLinearTopology.subringClass`).
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
open LieAlgebra.ofTwoCocycle (centralElement envelopingι adjoin_range_envelopingι)

namespace TauCeti.CurrentAlgebra

universe v

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  (Φ : LinearMap.BilinForm R L) (hΦ : Φ.lieInvariant L) (hΦs : Φ.IsSymm) (a : R)

local notation "c" => twoCocycleOfBilinear R L Φ hΦ hΦs
local notation "UK" => CentralQuotient R (centralElement c) a
local notation "Û" => CompletedEnveloping Φ hΦ hΦs a

/-! ### The topology of the center -/

/-- **The ideal `Z ∩ ker (Û → U / I_n)` of the completed center**: the central elements whose image
in `U / I_n` vanishes, that is, the preimage of the left ideal `ker (Û → U / I_n)` under the
inclusion of the center. -/
def centerOrderIdeal (n : ℕ) : Ideal (Subalgebra.center R Û) :=
  Ideal.comap (Subalgebra.center R Û).val (completedOrderLeftIdeal Φ hΦ hΦs a n)

variable {Φ hΦ hΦs a} in
@[simp]
theorem mem_centerOrderIdeal {n : ℕ} {z : Subalgebra.center R Û} :
    z ∈ centerOrderIdeal Φ hΦ hΦs a n ↔ (orderQuotientTower Φ hΦ hΦs a).limπ n z = 0 :=
  Ideal.mem_comap.trans mem_completedOrderLeftIdeal

/-- The ideals `Z ∩ ker (Û → U / I_n)` decrease as `n` grows. -/
theorem centerOrderIdeal_antitone : Antitone (centerOrderIdeal Φ hΦ hΦs a) :=
  fun _ _ h ↦ Ideal.comap_mono fun _ hx ↦ mem_completedOrderLeftIdeal.2 <| LinearMap.mem_ker.1 <|
    (orderQuotientTower Φ hΦ hΦs a).ker_limπ_antitone h <|
      LinearMap.mem_ker.2 (mem_completedOrderLeftIdeal.1 hx)

/-- The ideals `Z ∩ ker (Û → U / I_n)` form a basis of neighbourhoods of zero in the completed
center. -/
theorem hasBasis_nhds_zero_center :
    (𝓝 (0 : Subalgebra.center R Û)).HasBasis (fun _ : ℕ ↦ True)
      fun n ↦ (centerOrderIdeal Φ hΦ hΦs a n : Set (Subalgebra.center R Û)) := by
  rw [nhds_subtype, ZeroMemClass.coe_zero]
  exact (hasBasis_nhds_zero_completedOrderLeftIdeal Φ hΦ hΦs a).comap _

/-! ### Centrality on generators -/

/-- **The current generators topologically generate the completed enveloping algebra**: the
closure of the subalgebra generated by the images of the currents is all of `Û`. -/
theorem topologicalClosure_adjoin_range_envelopingι :
    (Algebra.adjoin R (Set.range
      (toCompletedEnveloping Φ hΦ hΦs a ∘ envelopingι c a))).topologicalClosure = ⊤ := by
  have hrange : Algebra.adjoin R (Set.range
      (toCompletedEnveloping Φ hΦ hΦs a ∘ envelopingι c a)) =
        (toCompletedEnveloping Φ hΦ hΦs a).range := by
    rw [Set.range_comp, ← AlgHom.map_adjoin, adjoin_range_envelopingι, Algebra.map_top]
  rw [hrange, SetLike.ext'_iff]
  simpa using (ModuleTower.denseRange_toLimQuotients _ _).closure_range

variable {Φ hΦ hΦs a}

/-- **Centrality in the completed enveloping algebra is detected on the current generators**: an
element of `Û` is central exactly when it commutes with the images of all currents. -/
theorem mem_center_iff_forall_commute {z : Û} :
    z ∈ Subalgebra.center R Û ↔
      ∀ u, Commute (toCompletedEnveloping Φ hΦ hΦs a (envelopingι c a u)) z := by
  rw [Subalgebra.mem_center_iff_forall_commute_of_topologicalClosure_adjoin_eq_top
    (topologicalClosure_adjoin_range_envelopingι Φ hΦ hΦs a), Set.forall_mem_range]
  simp only [Function.comp_apply]

/-! ### The action on smooth modules -/

section Action

variable
  {M N : ModuleCat.{v} (CentralQuotient R (centralElement (twoCocycleOfBilinear R L Φ hΦ hΦs)) a)}
  (hM : smoothModules (fun n : ℕ ↦ orderLeftIdeal Φ hΦ hΦs a n) M)
  (hN : smoothModules (fun n : ℕ ↦ orderLeftIdeal Φ hΦ hΦs a n) N)

/-- **Central elements of `Û` act on smooth modules by `U`-linear maps.** -/
theorem limSmul_smul_of_mem_center {z : Û} (hz : z ∈ Subalgebra.center R Û) (b : UK) (m : M) :
    ModuleTower.limSmul hM z (b • m) = b • ModuleTower.limSmul hM z m := by
  -- `b` acts as its image in `Û`, which commutes with `z`.
  rw [← limSmul_toCompletedEnveloping hM, ← limSmul_toCompletedEnveloping hM, ← mul_limSmul,
    ← mul_limSmul, Subalgebra.mem_center_iff.1 hz]

/-- **The action of the completed center on a smooth module.** A central element of `Û` acts on a
module over `U` which is smooth for the left ideals `I_n` by an endomorphism of `U`-modules. -/
def centerToModuleEnd : Subalgebra.center R Û →+* Module.End UK M where
  toFun z :=
    { toFun := ModuleTower.limSmul hM z
      map_add' := ModuleTower.limSmul_add hM z
      map_smul' := limSmul_smul_of_mem_center hM z.2 }
  map_one' := LinearMap.ext (one_limSmul hM)
  map_mul' z w := LinearMap.ext fun m ↦ mul_limSmul hM z w m
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
  rw [centerToModuleEnd_apply, centerToModuleEnd_apply, ← mul_limSmul, ← mul_limSmul,
    Subalgebra.mem_center_iff.1 z.2 x]

/-- The action of the completed center is natural: linear maps between smooth modules commute
with it. -/
theorem map_centerToModuleEnd (f : M →ₗ[UK] N) (z : Subalgebra.center R Û) (m : M) :
    f (centerToModuleEnd hM z m) = centerToModuleEnd hN z (f m) :=
  ModuleTower.map_limSmul hM hN f z m

end Action

end TauCeti.CurrentAlgebra
