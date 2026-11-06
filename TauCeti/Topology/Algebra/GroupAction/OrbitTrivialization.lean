/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.ConstMulAction
public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.Topology.FiberBundle.Trivialization

/-!
# Trivializations of orbit projections and orbit maps

Let a topological group `G` act continuously on `X`, and let `π : X → X ⧸ G` be the projection
to the orbit space, with its quotient topology. Over an open set `W` of orbits, a continuous map
`u : π⁻¹ W → G` with `u (g • x) = g * u x` trivializes `π` as a principal `G`-bundle: the map
`x ↦ (π x, u x)` is a homeomorphism `π⁻¹ W ≃ W × G`. Its inverse sends `(π x, g)` to
`(g * (u x)⁻¹) • x`; the point `(u x)⁻¹ • x` depends only on the orbit of `x`, so it defines a
continuous local section of `π` over `W`, by the universal property of the quotient topology.

This is the standard passage from an equivariant map to a local product structure for free
actions; see for instance Husemoller, *Fibre Bundles*, Chapter 4. It turns the construction of
equivariant maps into the construction of principal-bundle charts, using Mathlib's
`Trivialization`.

Dually, let `G` act on `X` and fix `x₀ : X`, with continuous orbit map `g ↦ g • x₀`. A section
`σ` of the orbit map, continuous on an open set `U ⊆ X` with `σ z • x₀ = z` on `U`, trivializes
the orbit map over `U` with fibre the stabilizer `H` of `x₀`: the map
`g ↦ (g • x₀, σ (g • x₀)⁻¹ * g)` is a homeomorphism from the preimage of `U` onto `U × H`, with
inverse `(z, h) ↦ σ z * h`, and it intertwines right multiplication by `H` on `G` with right
multiplication on the fibre. So the orbit map is a principal `H`-bundle over every open set
carrying a continuous local section, the classical way of exhibiting `G → G ⧸ H` as a principal
bundle (Steenrod, *The Topology of Fibre Bundles*, §7).

## Main definitions and results

* `TauCeti.orbitTrivialization`: the trivialization of the orbit projection over `W` determined
  by a continuous equivariant map `u : π⁻¹ W → G`.
* `TauCeti.orbitTrivialization_apply` and `TauCeti.orbitTrivialization_symm_apply_mk`: the chart
  and its inverse.
* `TauCeti.orbitTrivialization_apply_smul`: the chart intertwines the action on `X` with left
  multiplication on the fibre `G`.
* `TauCeti.orbitMapTrivialization`: the trivialization of the orbit map `g ↦ g • x₀` over `U`,
  with fibre the stabilizer of `x₀`, determined by a continuous local section over `U`.
* `TauCeti.orbitMapTrivialization_apply_mul`: the chart intertwines right multiplication by the
  stabilizer on `G` with right multiplication on the fibre.
-/

public section

open Bundle MulAction Set Topology

namespace TauCeti

variable {G X : Type*} [Group G] [MulAction G X] {W : Set (Quotient (orbitRel G X))} {u : X → G}

/-- The point `(u x)⁻¹ • x` only depends on the orbit of `x` when `u` is equivariant on a
saturated set containing `x`. -/
private theorem inv_smul_eq_of_smul_eq_mul
    (hu_smul : ∀ g : G, ∀ x ∈ Quotient.mk (orbitRel G X) ⁻¹' W, u (g • x) = g * u x)
    {x y : X} (hx : Quotient.mk (orbitRel G X) x ∈ W)
    (hxy : Quotient.mk (orbitRel G X) y = Quotient.mk (orbitRel G X) x) :
    (u y)⁻¹ • y = (u x)⁻¹ • x := by
  obtain ⟨g, rfl⟩ : ∃ g : G, g • x = y := Quotient.exact hxy
  rw [hu_smul g x hx, mul_inv_rev, mul_smul, inv_smul_smul]

variable [TopologicalSpace G] [ContinuousInv G] [TopologicalSpace X] [ContinuousSMul G X]

/-- The trivialization of the orbit projection `X → X ⧸ G` over an open set `W` of orbits,
determined by a continuous map `u : X → G` that is equivariant on the preimage of `W`. It sends
`x` to `(π x, u x)`, and its inverse sends `(π x, g)` to `(g * (u x)⁻¹) • x`. -/
noncomputable def orbitTrivialization (W : Set (Quotient (orbitRel G X))) (hW : IsOpen W)
    (u : X → G) (hu : ContinuousOn u (Quotient.mk (orbitRel G X) ⁻¹' W))
    (hu_smul : ∀ g : G, ∀ x ∈ Quotient.mk (orbitRel G X) ⁻¹' W, u (g • x) = g * u x) :
    Trivialization G (Quotient.mk (orbitRel G X)) where
  toFun x := (Quotient.mk _ x, u x)
  invFun p := p.2 • (u p.1.out)⁻¹ • p.1.out
  source := Quotient.mk (orbitRel G X) ⁻¹' W
  target := W ×ˢ univ
  map_source' _ hx := ⟨hx, mem_univ _⟩
  map_target' p hp := by simpa using hp.1
  left_inv' x hx := by
    simp only [inv_smul_eq_of_smul_eq_mul hu_smul hx (Quotient.out_eq _), smul_inv_smul]
  right_inv' p hp := by
    have hout : p.1.out ∈ Quotient.mk (orbitRel G X) ⁻¹' W := by simpa using hp.1
    have hsec : (u p.1.out)⁻¹ • p.1.out ∈ Quotient.mk (orbitRel G X) ⁻¹' W := by
      simpa using hp.1
    simp [hu_smul _ _ hsec, hu_smul _ _ hout]
  open_source := hW.preimage continuous_quot_mk
  open_target := hW.prod isOpen_univ
  continuousOn_toFun := continuous_quot_mk.continuousOn.prodMk hu
  continuousOn_invFun := by
    have hsec : ContinuousOn (fun y : Quotient (orbitRel G X) ↦ (u y.out)⁻¹ • y.out) W := by
      rw [isQuotientMap_quotient_mk'.continuousOn_isOpen_iff hW]
      refine ((hu.inv).smul continuousOn_id).congr fun x hx ↦ ?_
      exact inv_smul_eq_of_smul_eq_mul hu_smul hx (Quotient.out_eq _)
    exact continuousOn_snd.smul (hsec.comp continuousOn_fst fun _ hp ↦ hp.1)
  baseSet := W
  open_baseSet := hW
  source_eq := rfl
  target_eq := rfl
  proj_toFun _ _ := rfl

variable {hW : IsOpen W} {hu : ContinuousOn u (Quotient.mk (orbitRel G X) ⁻¹' W)}
  {hu_smul : ∀ g : G, ∀ x ∈ Quotient.mk (orbitRel G X) ⁻¹' W, u (g • x) = g * u x}

/-- `orbitTrivialization` sends `x` to its orbit together with `u x`. -/
@[simp]
theorem orbitTrivialization_apply (x : X) :
    orbitTrivialization W hW u hu hu_smul x = (Quotient.mk (orbitRel G X) x, u x) :=
  (rfl)

/-- The base of `orbitTrivialization` is the given open set of orbits. -/
@[simp]
theorem orbitTrivialization_baseSet : (orbitTrivialization W hW u hu hu_smul).baseSet = W :=
  (rfl)

/-- The inverse of `orbitTrivialization` sends `(π x, g)` to `(g * (u x)⁻¹) • x`. -/
@[simp]
theorem orbitTrivialization_symm_apply_mk {x : X} (hx : Quotient.mk (orbitRel G X) x ∈ W)
    (g : G) :
    (orbitTrivialization W hW u hu hu_smul).toOpenPartialHomeomorph.symm
      (Quotient.mk _ x, g) = (g * (u x)⁻¹) • x := by
  have hsrc : (g * (u x)⁻¹) • x ∈ (orbitTrivialization W hW u hu hu_smul).source := by
    simpa [Trivialization.mem_source] using hx
  have happly : orbitTrivialization W hW u hu hu_smul ((g * (u x)⁻¹) • x) =
      (Quotient.mk _ x, g) := by
    simp [hu_smul _ _ hx]
  rw [← happly]
  exact (orbitTrivialization W hW u hu hu_smul).toOpenPartialHomeomorph.left_inv hsrc

/-- `orbitTrivialization` intertwines the action of `G` on `X` with left multiplication on the
fibre `G`. -/
theorem orbitTrivialization_apply_smul (g : G) {x : X} (hx : Quotient.mk (orbitRel G X) x ∈ W) :
    orbitTrivialization W hW u hu hu_smul (g • x) =
      ((orbitTrivialization W hW u hu hu_smul x).1,
        g * (orbitTrivialization W hW u hu hu_smul x).2) := by
  simp only [orbitTrivialization_apply, hu_smul g x hx, orbitRel.Quotient.quotient_smul_eq]

/-! ### Trivializations of orbit maps from local sections -/

section OrbitMap

variable {G X : Type*} [Group G] [MulAction G X] {x₀ : X} {U : Set X} {σ : X → G}

/-- The fibre coordinate of `orbitMapTrivialization`: on the preimage of `U` it is
`σ (g • x₀)⁻¹ * g`, which fixes `x₀`, and elsewhere it is `1`. -/
private noncomputable def orbitMapFibre (x₀ : X) (U : Set X) (σ : X → G)
    (hσ_smul : ∀ z ∈ U, σ z • x₀ = z) (g : G) : stabilizer G x₀ :=
  letI := Classical.dec (g • x₀ ∈ U)
  if h : g • x₀ ∈ U then
    ⟨(σ (g • x₀))⁻¹ * g, by rw [mem_stabilizer_iff, mul_smul, inv_smul_eq_iff, hσ_smul _ h]⟩
  else 1

private theorem coe_orbitMapFibre {hσ_smul : ∀ z ∈ U, σ z • x₀ = z} {g : G} (hg : g • x₀ ∈ U) :
    (orbitMapFibre x₀ U σ hσ_smul g : G) = (σ (g • x₀))⁻¹ * g := by
  simp only [orbitMapFibre, hg, ↓reduceDIte]

variable [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace X]

/-- The trivialization of the orbit map `g ↦ g • x₀` over an open set `U`, with fibre the
stabilizer of `x₀`, determined by a section `σ` of the orbit map continuous on `U`. It sends `g`
over `U` to `(g • x₀, σ (g • x₀)⁻¹ * g)`, and its inverse sends `(z, h)` to `σ z * h`. -/
noncomputable def orbitMapTrivialization (x₀ : X) (hx₀ : Continuous fun g : G ↦ g • x₀)
    (U : Set X) (hU : IsOpen U) (σ : X → G) (hσ : ContinuousOn σ U)
    (hσ_smul : ∀ z ∈ U, σ z • x₀ = z) :
    Trivialization (stabilizer G x₀) fun g : G ↦ g • x₀ where
  toFun g := (g • x₀, orbitMapFibre x₀ U σ hσ_smul g)
  invFun p := σ p.1 * p.2
  source := (fun g : G ↦ g • x₀) ⁻¹' U
  target := U ×ˢ univ
  map_source' _ hg := ⟨hg, mem_univ _⟩
  map_target' p hp := by
    rw [mem_preimage, mul_smul, mem_stabilizer_iff.1 p.2.2, hσ_smul _ hp.1]
    exact hp.1
  left_inv' g hg := by
    simp only [coe_orbitMapFibre hg, mul_inv_cancel_left]
  right_inv' p hp := by
    have hp' : (σ p.1 * p.2) • x₀ = p.1 := by
      rw [mul_smul, mem_stabilizer_iff.1 p.2.2, hσ_smul _ hp.1]
    have hmem : (σ p.1 * p.2) • x₀ ∈ U := hp'.symm ▸ hp.1
    refine Prod.ext hp' (Subtype.ext ?_)
    rw [coe_orbitMapFibre hmem, hp', inv_mul_cancel_left]
  open_source := hU.preimage hx₀
  open_target := hU.prod isOpen_univ
  continuousOn_toFun := by
    refine hx₀.continuousOn.prodMk ?_
    rw [Topology.IsInducing.subtypeVal.continuousOn_iff]
    exact ((hσ.comp hx₀.continuousOn fun _ hg ↦ hg).inv.mul continuousOn_id).congr
      fun g hg ↦ coe_orbitMapFibre hg
  continuousOn_invFun :=
    (hσ.comp (continuousOn_fst (s := U ×ˢ univ)) fun _ hp ↦ hp.1).mul
      (continuous_subtype_val.comp_continuousOn continuousOn_snd)
  baseSet := U
  open_baseSet := hU
  source_eq := rfl
  target_eq := rfl
  proj_toFun _ _ := rfl

variable {hx₀ : Continuous fun g : G ↦ g • x₀} {hU : IsOpen U} {hσ : ContinuousOn σ U}
  {hσ_smul : ∀ z ∈ U, σ z • x₀ = z}

/-- Over `U`, `orbitMapTrivialization` sends `g` to `(g • x₀, σ (g • x₀)⁻¹ * g)`. -/
theorem orbitMapTrivialization_apply {g : G} (hg : g • x₀ ∈ U) :
    orbitMapTrivialization x₀ hx₀ U hU σ hσ hσ_smul g =
      (g • x₀, ⟨(σ (g • x₀))⁻¹ * g, by
        rw [mem_stabilizer_iff, mul_smul, inv_smul_eq_iff, hσ_smul _ hg]⟩) :=
  Prod.ext rfl (Subtype.ext (coe_orbitMapFibre (hσ_smul := hσ_smul) hg))

/-- The inverse of `orbitMapTrivialization` sends `(z, h)` to `σ z * h`. -/
@[simp]
theorem orbitMapTrivialization_symm_apply (p : X × stabilizer G x₀) :
    (orbitMapTrivialization x₀ hx₀ U hU σ hσ hσ_smul).toOpenPartialHomeomorph.symm p =
      σ p.1 * p.2 :=
  (rfl)

/-- The base of `orbitMapTrivialization` is the open set carrying the section. -/
@[simp]
theorem orbitMapTrivialization_baseSet :
    (orbitMapTrivialization x₀ hx₀ U hU σ hσ hσ_smul).baseSet = U :=
  (rfl)

/-- `orbitMapTrivialization` intertwines right multiplication by the stabilizer of `x₀` on `G`
with right multiplication on the fibre. -/
theorem orbitMapTrivialization_apply_mul {g : G} (hg : g • x₀ ∈ U) (h : stabilizer G x₀) :
    orbitMapTrivialization x₀ hx₀ U hU σ hσ hσ_smul (g * h) =
      ((orbitMapTrivialization x₀ hx₀ U hU σ hσ hσ_smul g).1,
        (orbitMapTrivialization x₀ hx₀ U hU σ hσ hσ_smul g).2 * h) := by
  have hgh : (g * h) • x₀ = g • x₀ := by rw [mul_smul, mem_stabilizer_iff.1 h.2]
  rw [orbitMapTrivialization_apply hg, orbitMapTrivialization_apply (hgh.symm ▸ hg)]
  refine Prod.ext hgh (Subtype.ext ?_)
  simp only [Subgroup.coe_mul, hgh, mul_assoc]

end OrbitMap

end TauCeti
