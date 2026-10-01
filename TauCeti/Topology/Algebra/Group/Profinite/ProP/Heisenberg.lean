/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.ContinuousMulEquiv
public import TauCeti.GroupTheory.GroupExtension.Of.Surjective
public import TauCeti.Topology.Algebra.Group.Heisenberg
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.Extension
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.PadicInt.Basic
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.Product
public import TauCeti.Topology.Separation.TypeTags

/-!
# The Heisenberg group over a pro-`p` ring is pro-`p`

Let `R` be a compact Hausdorff topological ring whose additive group is pro-`p`. Then the
Heisenberg group `HeisenbergGroup R`, with the topology of `R × R × R`, is pro-`p`
(`TauCeti.HeisenbergGroup.isProP`). It is an extension

  `1 → R → HeisenbergGroup R → R × R → 1`,

where `R` embeds as the central `z`-axis `(0, 0, z)` and the quotient map forgets the
`z`-coordinate, and pro-`p` groups are closed under extensions with compact total group
(`TauCeti.IsProP.of_ker_isProP`).

Over the `p`-adic integers this gives the compact, totally disconnected pro-`p` group
`HeisenbergGroup ℤ_[p]` of nilpotency class two (`TauCeti.HeisenbergGroup.isProP_padicInt`). By the
universal property of free pro-`p` groups it receives a continuous homomorphism from a free pro-`p`
group sending two chosen generators to `(1, 0, 0)` and `(0, 1, 0)`; since their commutator is
`(0, 0, 1)`, this detects the brackets of generators in the graded Lie ring of the closed lower
central series of a free pro-`p` group. Two facts make the detection work: the closed lower
central series of the Heisenberg group over a Hausdorff topological ring stops at `γ_2 = 1`
(`TauCeti.HeisenbergGroup.closedLowerCentralSeries_two_eq_bot`), and the `p`-adic powers of
`(0, 0, z)` are the elements `(0, 0, c z)`.

## Main results

* `TauCeti.HeisenbergGroup.isProP`: the Heisenberg group over a compact Hausdorff topological ring
  with pro-`p` additive group is pro-`p`.
* `TauCeti.HeisenbergGroup.isProP_padicInt`: the Heisenberg group over `ℤ_[p]` is pro-`p`.
* `TauCeti.HeisenbergGroup.padicPow_mk_zero_zero`: the `p`-adic power of `(0, 0, z)` by `c` is
  `(0, 0, c z)`.

## References

* L. Ribes and P. Zalesskii, *Profinite Groups*, 2nd ed., Section 2.2.
-/

public section

namespace TauCeti

namespace HeisenbergGroup

open Multiplicative

variable {p : ℕ} {R : Type*} [Ring R] [TopologicalSpace R] [IsTopologicalRing R]
  [CompactSpace R] [T2Space R]

/-- The Heisenberg group over a compact Hausdorff topological ring whose additive group is
pro-`p` is pro-`p`. -/
theorem isProP (hR : IsProP p (Multiplicative R)) : IsProP p (HeisenbergGroup R) := by
  classical
  -- The quotient map `(x, y, z) ↦ (x, y)` onto `R × R`, whose kernel is the `z`-axis.
  let f : HeisenbergGroup R →* Multiplicative (R × R) :=
    { toFun a := ofAdd (a.x, a.y)
      map_one' := by simp
      map_mul' a b := by simp [← ofAdd_add] }
  -- The inclusion `z ↦ (0, 0, z)` of `R` onto the `z`-axis.
  let g : Multiplicative R →* HeisenbergGroup R :=
    { toFun c := ⟨0, 0, c.toAdd⟩
      map_one' := by ext <;> simp
      map_mul' a b := by ext <;> simp }
  have hf : Continuous f :=
    continuous_ofAdd.comp (continuous_x.prodMk continuous_y)
  have hg : Continuous g :=
    continuous_iff.mpr ⟨continuous_const, continuous_const, continuous_toAdd⟩
  have hker : f.ker = zAxis := by
    ext a
    simp [f, mem_zAxis_iff]
  have hgf : ∀ c, g c ∈ f.ker := by
    intro c
    simp [f, g]
  let gker := g.codRestrict f.ker hgf
  have hgker : Function.Bijective gker := by
    constructor
    · intro a b hab
      have hz := congrArg (fun c : f.ker ↦ c.val.z) hab
      simpa [gker, g] using hz
    · rintro ⟨a, ha⟩
      have hxy := mem_zAxis_iff.mp (hker ▸ ha)
      refine ⟨ofAdd a.z, ?_⟩
      apply Subtype.ext
      ext <;> simp [gker, g, hxy]
  let e : Multiplicative R ≃* f.ker := MulEquiv.ofBijective gker hgker
  have hsurj : Function.Surjective f := by
    intro c
    exact ⟨⟨c.toAdd.1, c.toAdd.2, 0⟩, by simp [f]⟩
  let S : GroupExtension (Multiplicative R) (HeisenbergGroup R)
      (Multiplicative (R × R)) :=
    GroupExtension.ofMulEquivKer hsurj e
  have hSinl : S.inl = g := by
    simp only [S, GroupExtension.ofMulEquivKer_inl]
    apply MonoidHom.ext
    intro c
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, Subgroup.subtype_apply,
      e, MulEquiv.ofBijective_apply, gker, MonoidHom.codRestrict_apply]
  have hSrh : S.rightHom = f :=
    GroupExtension.ofMulEquivKer_rightHom _ _
  have hRR : IsProP p (Multiplicative (R × R)) :=
    (hR.prod hR).of_equiv (ContinuousMulEquiv.prodMultiplicative R R).symm
  exact S.isProP (hSinl ▸ hg) (hSrh ▸ hf) hR hRR

/-- The Heisenberg group over the `p`-adic integers is pro-`p`. -/
theorem isProP_padicInt (p : ℕ) [Fact p.Prime] : IsProP p (HeisenbergGroup ℤ_[p]) :=
  isProP (isProP_multiplicative_padicInt p)

/-- The `p`-adic power of an element `(0, 0, z)` of the `z`-axis of the Heisenberg group over
`ℤ_[p]` by `c` is `(0, 0, c z)`. -/
@[simp]
theorem padicPow_mk_zero_zero {p : ℕ} [Fact p.Prime] (z c : ℤ_[p]) :
    (isProP_padicInt p).padicPow ⟨0, 0, z⟩ c = ⟨0, 0, c * z⟩ := by
  -- The continuous homomorphism `c ↦ (0, 0, c z)` out of `ℤ_[p]` sends `1` to `(0, 0, z)`.
  let g : Multiplicative ℤ_[p] →* HeisenbergGroup ℤ_[p] :=
    { toFun c := ⟨0, 0, c.toAdd * z⟩
      map_one' := by ext <;> simp
      map_mul' a b := by ext <;> simp [add_mul] }
  have hg : Continuous g :=
    continuous_iff.mpr ⟨continuous_const, continuous_const,
      (continuous_toAdd.mul continuous_const : Continuous fun c : Multiplicative ℤ_[p] ↦
        c.toAdd * z)⟩
  have h := (isProP_multiplicative_padicInt p).map_padicPow (isProP_padicInt p) g hg (ofAdd 1) c
  simpa [g] using h.symm

end HeisenbergGroup

end TauCeti
