/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.Compact
public import TauCeti.LinearAlgebra.Quotient.PiSpanSingleton
public import TauCeti.RingTheory.Valuation.FinsetDvd
public import TauCeti.Topology.Algebra.Module.PiSpanSingleton
public import TauCeti.Topology.Algebra.Group.Profinite.Free.Abelianization
public import TauCeti.Topology.Algebra.Group.Profinite.Presentation.Basic
public import TauCeti.Topology.Separation.TypeTags

/-!
# The abelianization of a presented pro-`p` group, and the one-relator structure theorem

Let `G = presentedProP p X rels` be the pro-`p` group presented on a finite type `X` by a set of
relators `rels ⊆ F = freeProP p X`. Abelianizing the presentation gives a continuous surjection

`abelianizationHom rels : ℤ_p^X → G^{ab},   u ↦ ∏ x, x_x ^ (u x)`,

the composite of the abelianization isomorphism `F^{ab} ≅ ℤ_p^X` of
`TauCeti.freeProP.abelianizationEquiv` with the map `F^{ab} → G^{ab}` induced by the presentation,
whose kernel is the image of the closed normal closure of the relators.

For a **single relator** `r` the kernel is computed exactly: it is the `ℤ_p`-span of the exponent
vector `v = exponentSum r` of the relator, because the closed normal closure of `r` maps onto the
`p`-adic powers of the class of `r`, which are the `ℤ_p`-multiples of `v`
(`abelianizationHom_ofAdd_eq_one_iff`). Writing `v = q • w` with `w x₀ = 1` — which is possible as
soon as the coordinate `v x₀` divides all the others, and some coordinate does since `ℤ_p` is a
valuation ring — the change of basis `TauCeti.LinearEquiv.piSplitAt` then identifies
`ℤ_p^X ⧸ ℤ_p v` with `ℤ_p^{X ∖ {x₀}} × ℤ_p ⧸ (q)`. This is the **abelianization structure theorem
for one-relator pro-`p` groups** (`oneRelatorAbelianizationEquiv`):

`G^{ab} ≅ ℤ_p^{n-1} × ℤ_p ⧸ q ℤ_p,   n = #X, q = v x₀`.

Here `q : ℤ_p` is a coordinate of the exponent vector, determined by the relator only up to a
unit of `ℤ_p`; the factor `ℤ_p ⧸ q ℤ_p` depends only on the ideal `q ℤ_p`, that is on the valuation
of `q`. One has `q = 0` exactly when the relator lies in the closed commutator subgroup, and then
`G^{ab} ≅ ℤ_p^n` is torsion-free. When `q ≠ 0` the factor `ℤ_p ⧸ q ℤ_p` is finite cyclic of order
`p^{v_p(q)}` and is the torsion subgroup of `G^{ab}`. For a Demushkin group, whose minimal
presentation has a single relator, this is Labute's description `G ⧸ [G, G] ≅ ℤ_p^{n-1} ⊕ ℤ ⧸ q(G)`
of the abelianization: the integer invariant `q(G) ∈ {0} ∪ p^ℕ` of the classification is not the
coordinate `q` itself but the normalised generator `p^{v_p(q)}` of the ideal `q ℤ_p`, that is the
order of the torsion subgroup of `G^{ab}`, and it is `0` when `q = 0`.

## Main definitions

* `TauCeti.presentedProP.abelianizationHom`: the continuous surjection `ℤ_p^X → G^{ab}` induced by
  a presentation.
* `TauCeti.presentedProP.oneRelatorAbelianizationEquiv`: for `G = ⟨X ∣ r⟩` with
  `exponentSum r = q • w` and `w x₀ = 1`, the topological isomorphism
  `G^{ab} ≃ₜ* ℤ_p^{X ∖ {x₀}} × ℤ_p ⧸ (q)`.

## Main results

* `TauCeti.presentedProP.abelianizationHom_surjective`,
  `TauCeti.presentedProP.abelianizationHom_ofAdd`: the map is surjective and is
  `u ↦ ∏ x, x_x ^ (u x)`.
* `TauCeti.presentedProP.abelianizationHom_ofAdd_eq_one_iff`: for a single relator `r`, the
  kernel is the `ℤ_p`-span of the exponent vector of `r`.
* `TauCeti.presentedProP.oneRelatorAbelianizationEquiv_abelianizationHom_ofAdd`: the isomorphism
  composed with `abelianizationHom` is the reduction `TauCeti.LinearMap.piSplitAtQuot` of the
  exponent vectors.
* `TauCeti.presentedProP.oneRelatorAbelianizationEquiv_mk_of_ne`,
  `TauCeti.presentedProP.oneRelatorAbelianizationEquiv_mk_of_self`,
  `TauCeti.presentedProP.oneRelatorAbelianizationEquiv_symm_ofAdd_mk`: the values of the
  isomorphism on the generators and of its inverse.
* `TauCeti.presentedProP.oneRelator_q_eq_zero_iff_mem_topologicalClosure_commutator`: `q = 0`
  exactly when the relator lies in the closed commutator subgroup of the free pro-`p` group.
* `TauCeti.presentedProP.exists_nonempty_oneRelatorAbelianizationEquiv`: for nonempty `X`, some
  coordinate `x₀` of the exponent vector divides all the others, and the isomorphism exists with
  `q` that coordinate.

## References

* J. P. Labute, *Classification of Demushkin groups*, Canad. J. Math. 19 (1967), 106–132, p. 106.
* J. Neukirch, A. Schmidt and K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Chapter III,
  §9.
-/

public section

namespace TauCeti

open Multiplicative

universe u

variable {p : ℕ} [Fact p.Prime] {X : Type u}

namespace presentedProP

variable (rels : Set (freeProP p X))

omit [Fact p.Prime] in
private theorem coe_mk_apply (y : freeProP p X) :
    (mk p rels : freeProP p X →* presentedProP p X rels) y = mk p rels y :=
  (rfl)

section Hom

variable [Fintype X]

/-- **The abelianization map of a presentation.** For `G = presentedProP p X rels`, the continuous
homomorphism `ℤ_p^X → G^{ab}` sending `u` to `∏ x, x_x ^ (u x)`, the product of the `p`-adic
powers of the classes of the generators (`TauCeti.presentedProP.abelianizationHom_ofAdd`). It is
the composite of the inverse of `TauCeti.freeProP.abelianizationEquiv` with the map
`F^{ab} → G^{ab}` induced by the presentation, and it is surjective. -/
noncomputable def abelianizationHom :
    Multiplicative (X → ℤ_[p]) →ₜ* TopologicalAbelianization (presentedProP p X rels) :=
  -- `TopologicalAbelianization.map` takes the continuity proof at the `→*` coercion of `mk p rels`,
  -- and the rewrites with `map_mk` below match `hf` syntactically at implicit transparency; the
  -- field `(mk p rels).continuous` has the defeq but distinct type `Continuous ⇑(mk p rels)`, so
  -- it is passed through `show` at the required type here and at every `map (mk p rels) _` below.
  (⟨TopologicalAbelianization.map (mk p rels : freeProP p X →* presentedProP p X rels)
      (show Continuous ⇑(mk p rels : freeProP p X →* presentedProP p X rels) from
        (mk p rels).continuous),
    TopologicalAbelianization.continuous_map _ _⟩ :
    TopologicalAbelianization (freeProP p X) →ₜ*
      TopologicalAbelianization (presentedProP p X rels)).comp
    ((freeProP.abelianizationEquiv p X).symm :
      Multiplicative (X → ℤ_[p]) →ₜ* TopologicalAbelianization (freeProP p X))

theorem abelianizationHom_apply (u : Multiplicative (X → ℤ_[p])) :
    abelianizationHom rels u =
      TopologicalAbelianization.map (mk p rels : freeProP p X →* presentedProP p X rels)
        (show Continuous ⇑(mk p rels : freeProP p X →* presentedProP p X rels) from
          (mk p rels).continuous)
        ((freeProP.abelianizationEquiv p X).symm u) :=
  (rfl)

/-- The abelianization map of a presentation composed with the exponent-sum map of the free group
is the passage to the class in `G^{ab}`. -/
theorem abelianizationHom_exponentSum (y : freeProP p X) :
    abelianizationHom rels (freeProP.exponentSum p X y) =
      ((mk p rels y : presentedProP p X rels) :
        TopologicalAbelianization (presentedProP p X rels)) := by
  rw [abelianizationHom_apply, ← freeProP.abelianizationEquiv_mk,
    ContinuousMulEquiv.symm_apply_apply, TopologicalAbelianization.map_mk, coe_mk_apply]

/-- The abelianization map of a presentation sends the coordinate vector at `x` to the class of the
generator at `x`. -/
@[simp]
theorem abelianizationHom_ofAdd_single [DecidableEq X] (x : X) :
    abelianizationHom rels (ofAdd (Pi.single x 1)) =
      ((of p rels x : presentedProP p X rels) :
        TopologicalAbelianization (presentedProP p X rels)) := by
  rw [← freeProP.exponentSum_of, abelianizationHom_exponentSum, mk_of]

/-- The abelianization map of a presentation is surjective. -/
theorem abelianizationHom_surjective : Function.Surjective (abelianizationHom rels) := by
  intro g
  obtain ⟨y, hy⟩ := TopologicalAbelianization.map_surjective
    (mk p rels : freeProP p X →* presentedProP p X rels)
    (show Continuous ⇑(mk p rels : freeProP p X →* presentedProP p X rels) from
      (mk p rels).continuous)
    (mk_surjective p rels) g
  exact ⟨freeProP.abelianizationEquiv p X y, by
    rw [abelianizationHom_apply, ContinuousMulEquiv.symm_apply_apply, hy]⟩

/-- The abelianization map of a presentation is `u ↦ ∏ x, x_x ^ (u x)`, the product of the
`p`-adic powers of the classes of the generators in the abelian pro-`p` group `G^{ab}`. -/
theorem abelianizationHom_ofAdd (u : X → ℤ_[p]) :
    abelianizationHom rels (ofAdd u) =
      ∏ x, (isProP p X rels).topologicalAbelianization.padicPow
        ((of p rels x : presentedProP p X rels) :
          TopologicalAbelianization (presentedProP p X rels)) (u x) := by
  rw [abelianizationHom_apply, freeProP.abelianizationEquiv_symm_ofAdd, map_prod]
  refine Finset.prod_congr rfl fun x _ ↦ ?_
  rw [(isProP_freeProP p X).topologicalAbelianization.map_padicPow
    (isProP p X rels).topologicalAbelianization
    (TopologicalAbelianization.map (mk p rels : freeProP p X →* presentedProP p X rels)
      (show Continuous ⇑(mk p rels : freeProP p X →* presentedProP p X rels) from
        (mk p rels).continuous))
    (TopologicalAbelianization.continuous_map _ _),
    TopologicalAbelianization.map_mk, coe_mk_apply, mk_of]

variable (r : freeProP p X)

/-- **The kernel of the abelianization map of a one-relator presentation** is the `ℤ_p`-span of the
exponent vector of the relator: for `G = ⟨X ∣ r⟩` and `u : X → ℤ_p`, the element `∏ x, x_x ^ (u x)`
of `G^{ab}` is trivial exactly when `u` is a `ℤ_p`-multiple of `exponentSum r`. -/
theorem abelianizationHom_ofAdd_eq_one_iff (u : X → ℤ_[p]) :
    abelianizationHom {r} (ofAdd u) = 1 ↔
      u ∈ Submodule.span ℤ_[p] {(freeProP.exponentSum p X r).toAdd} := by
  set v := (freeProP.exponentSum p X r).toAdd with hv
  have hF := (isProP_freeProP p X).topologicalAbelianization
  have hG := (isProP p X {r}).topologicalAbelianization
  set ρ : TopologicalAbelianization (freeProP p X) := (r : TopologicalAbelianization (freeProP p X))
    with hρ
  have hερ : freeProP.abelianizationEquiv p X ρ = ofAdd v := by
    rw [hρ, freeProP.abelianizationEquiv_mk, hv, ofAdd_toAdd]
  -- The abelianization isomorphism carries the `p`-adic powers of `ρ` to the multiples of `v`.
  have hpow : ∀ l : ℤ_[p], freeProP.abelianizationEquiv p X (hF.padicPow ρ l) = ofAdd (l • v) := by
    intro l
    have h := hF.map_padicPow (isProP_multiplicative_pi_padicInt p X)
      (freeProP.abelianizationEquiv p X : TopologicalAbelianization (freeProP p X) →*
        Multiplicative (X → ℤ_[p]))
      (freeProP.abelianizationEquiv p X).continuous ρ l
    rw [MonoidHom.coe_coe] at h
    rw [h, hερ, IsProP.padicPow_ofAdd_pi]
  constructor
  · intro h
    -- The image of `u` in `F^{ab}` lies in the kernel of `F^{ab} → G^{ab}`, which is the image of
    -- the closed normal closure `R` of `r`.
    have hmem : (freeProP.abelianizationEquiv p X).symm (ofAdd u) ∈
        (TopologicalAbelianization.map (mk p {r} : freeProP p X →* presentedProP p X {r})
          (show Continuous ⇑(mk p {r} : freeProP p X →* presentedProP p X {r}) from
            (mk p {r}).continuous)).ker := by
      rw [MonoidHom.mem_ker, ← abelianizationHom_apply]
      exact h
    rw [TopologicalAbelianization.ker_map_of_surjective
      (mk p {r} : freeProP p X →* presentedProP p X {r})
      (show Continuous ⇑(mk p {r} : freeProP p X →* presentedProP p X {r}) from
        (mk p {r}).continuous)
      (mk_surjective p {r}), ker_mk] at hmem
    obtain ⟨y, hy, hyu⟩ := hmem
    -- `R` lies in the preimage of the closed subgroup of `p`-adic powers of `ρ`.
    have hK : (Subgroup.normalClosure {r}).topologicalClosure ≤
        ((hF.padicPowHom ρ :
          Multiplicative ℤ_[p] →* TopologicalAbelianization (freeProP p X)).range).comap
            (QuotientGroup.mk' (commutator (freeProP p X)).topologicalClosure) := by
      refine Subgroup.topologicalClosure_minimal _ (Subgroup.normalClosure_le_normal ?_) ?_
      · rw [Set.singleton_subset_iff, SetLike.mem_coe, Subgroup.mem_comap, MonoidHom.mem_range]
        exact ⟨ofAdd 1, by
          rw [MonoidHom.coe_coe, hF.padicPowHom_ofAdd_one, QuotientGroup.mk'_apply, hρ]⟩
      · rw [Subgroup.coe_comap, MonoidHom.coe_range, MonoidHom.coe_coe]
        exact ((isCompact_range (hF.padicPowHom ρ).continuous).isClosed).preimage
          continuous_quot_mk
    obtain ⟨l, hl⟩ := MonoidHom.mem_range.mp (Subgroup.mem_comap.mp (hK hy))
    refine Submodule.mem_span_singleton.mpr ⟨l.toAdd, ?_⟩
    have h' := congrArg (freeProP.abelianizationEquiv p X) hyu
    rw [ContinuousMulEquiv.apply_symm_apply, ← hl, MonoidHom.coe_coe, hF.padicPowHom_apply,
      hpow] at h'
    exact ofAdd.injective h'
  · intro hu
    obtain ⟨l, rfl⟩ := Submodule.mem_span_singleton.mp hu
    have h1 : (mk p {r} : freeProP p X →* presentedProP p X {r}) r = 1 :=
      mk_relator r (Set.mem_singleton r)
    rw [abelianizationHom_apply, ← hpow, ContinuousMulEquiv.symm_apply_apply,
      hF.map_padicPow hG
        (TopologicalAbelianization.map (mk p {r} : freeProP p X →* presentedProP p X {r})
          (show Continuous ⇑(mk p {r} : freeProP p X →* presentedProP p X {r}) from
            (mk p {r}).continuous))
        (TopologicalAbelianization.continuous_map _ _),
      TopologicalAbelianization.map_mk, h1, QuotientGroup.mk_one, IsProP.one_padicPow]

end Hom

section OneRelator

open TauCeti.ContinuousMonoidHom (piSplitAtQuotMultiplicative piSplitAtQuotMultiplicative_ofAdd)

variable (r : freeProP p X) (x₀ : X) (w : X → ℤ_[p]) (hw : w x₀ = 1) (q : ℤ_[p])

variable (hr : (freeProP.exponentSum p X r).toAdd = q • w)

include hr in
private theorem piSplitAtQuotMultiplicative_exponentSum_relator :
    piSplitAtQuotMultiplicative x₀ w hw q (freeProP.exponentSum p X r) = 1 := by
  rw [← ofAdd_toAdd (freeProP.exponentSum p X r), hr, piSplitAtQuotMultiplicative_ofAdd,
    ofAdd_eq_one, ← LinearMap.mem_ker, LinearMap.ker_piSplitAtQuot]
  exact Submodule.mem_span_singleton_self _

include hr in
/-- The homomorphism `G^{ab} → ℤ_p^{X ∖ {x₀}} × ℤ_p ⧸ (q)` induced by the reduction of the exponent
vectors; it is the underlying map of `oneRelatorAbelianizationEquiv`. -/
private noncomputable def toSplitQuot :
    TopologicalAbelianization (presentedProP p X {r}) →ₜ*
      Multiplicative (({x // x ≠ x₀} → ℤ_[p]) × (ℤ_[p] ⧸ Ideal.span {q})) :=
  TopologicalAbelianization.lift
    (lift ((piSplitAtQuotMultiplicative x₀ w hw q).comp (freeProP.exponentSum p X)) fun s hs ↦ by
      rw [Set.mem_singleton_iff.mp hs, ContinuousMonoidHom.coe_comp, Function.comp_apply]
      exact piSplitAtQuotMultiplicative_exponentSum_relator r x₀ w hw q hr)

private theorem toSplitQuot_mk (y : freeProP p X) :
    toSplitQuot r x₀ w hw q hr
        ((mk p {r} y : presentedProP p X {r}) : TopologicalAbelianization (presentedProP p X {r})) =
      piSplitAtQuotMultiplicative x₀ w hw q (freeProP.exponentSum p X y) := by
  refine (TopologicalAbelianization.lift_mk _ _).trans ?_
  rw [lift_mk, ContinuousMonoidHom.coe_comp, Function.comp_apply]

private theorem toSplitQuot_abelianizationHom [Fintype X] (u : Multiplicative (X → ℤ_[p])) :
    toSplitQuot r x₀ w hw q hr (abelianizationHom {r} u) =
      piSplitAtQuotMultiplicative x₀ w hw q u := by
  classical
  have h : (toSplitQuot r x₀ w hw q hr).comp (abelianizationHom {r}) =
      piSplitAtQuotMultiplicative x₀ w hw q :=
    continuousMonoidHom_ext_multiplicative_pi_padicInt p X fun x ↦ by
      rw [ContinuousMonoidHom.coe_comp, Function.comp_apply, abelianizationHom_ofAdd_single,
        ← mk_of, toSplitQuot_mk, freeProP.exponentSum_of]
  have := DFunLike.congr_fun h u
  rwa [ContinuousMonoidHom.coe_comp, Function.comp_apply] at this

variable [Finite X]

private theorem toSplitQuot_bijective : Function.Bijective (toSplitQuot r x₀ w hw q hr) := by
  cases nonempty_fintype X
  constructor
  · intro g g' hgg'
    obtain ⟨u, rfl⟩ := abelianizationHom_surjective {r} g
    obtain ⟨u', rfl⟩ := abelianizationHom_surjective {r} g'
    rw [toSplitQuot_abelianizationHom, toSplitQuot_abelianizationHom] at hgg'
    have h1 : piSplitAtQuotMultiplicative x₀ w hw q (u / u') = 1 := by
      rw [map_div, hgg', div_self']
    rw [← ofAdd_toAdd (u / u'), piSplitAtQuotMultiplicative_ofAdd, ofAdd_eq_one,
      ← LinearMap.mem_ker, LinearMap.ker_piSplitAtQuot, ← hr] at h1
    have h2 := (abelianizationHom_ofAdd_eq_one_iff r _).mpr h1
    rwa [ofAdd_toAdd, map_div, div_eq_one] at h2
  · intro t
    obtain ⟨u, hu⟩ := LinearMap.piSplitAtQuot_surjective x₀ w hw q t.toAdd
    exact ⟨abelianizationHom {r} (ofAdd u), by
      rw [toSplitQuot_abelianizationHom, piSplitAtQuotMultiplicative_ofAdd, hu, ofAdd_toAdd]⟩

/-- **The abelianization structure theorem for one-relator pro-`p` groups.** Let
`G = presentedProP p X {r}` be the pro-`p` group on a finite type `X` with the single relator `r`,
and write the exponent vector of `r` as `exponentSum r = q • w` with `w x₀ = 1`. Then

`G^{ab} ≃ₜ* ℤ_p^{X ∖ {x₀}} × ℤ_p ⧸ q ℤ_p`

as topological groups, the isomorphism sending the class of the generator at `x ≠ x₀` to the
coordinate vector at `x` and the class of the generator at `x₀` to `(-w, 1)`. When `q ≠ 0` the
factor `ℤ_p ⧸ q ℤ_p` is finite cyclic and is the torsion subgroup of `G^{ab}`; when `q = 0` it is
`ℤ_p` and `G^{ab} ≅ ℤ_p^X` is torsion-free. -/
noncomputable def oneRelatorAbelianizationEquiv :
    TopologicalAbelianization (presentedProP p X {r}) ≃ₜ*
      Multiplicative (({x // x ≠ x₀} → ℤ_[p]) × (ℤ_[p] ⧸ Ideal.span {q})) :=
  let e := MulEquiv.ofBijective
    (toSplitQuot r x₀ w hw q hr : TopologicalAbelianization (presentedProP p X {r}) →*
      Multiplicative (({x // x ≠ x₀} → ℤ_[p]) × (ℤ_[p] ⧸ Ideal.span {q})))
    (toSplitQuot_bijective r x₀ w hw q hr)
  { toMulEquiv := e
    continuous_toFun := (toSplitQuot r x₀ w hw q hr).continuous
    continuous_invFun :=
      Continuous.continuous_symm_of_equiv_compact_to_t2 (f := e.toEquiv)
        (toSplitQuot r x₀ w hw q hr).continuous }

private theorem oneRelatorAbelianizationEquiv_apply
    (g : TopologicalAbelianization (presentedProP p X {r})) :
    oneRelatorAbelianizationEquiv r x₀ w hw q hr g = toSplitQuot r x₀ w hw q hr g :=
  (rfl)

/-- The abelianization isomorphism of a one-relator group sends the class of `mk y` to the
reduction of the exponent vector of `y`. -/
@[simp]
theorem oneRelatorAbelianizationEquiv_mk (y : freeProP p X) :
    oneRelatorAbelianizationEquiv r x₀ w hw q hr
        ((mk p {r} y : presentedProP p X {r}) : TopologicalAbelianization (presentedProP p X {r})) =
      ofAdd (LinearMap.piSplitAtQuot x₀ w hw q (freeProP.exponentSum p X y).toAdd) := by
  rw [oneRelatorAbelianizationEquiv_apply, toSplitQuot_mk, ← piSplitAtQuotMultiplicative_ofAdd,
    ofAdd_toAdd]

/-- The abelianization isomorphism of a one-relator group composed with the abelianization map of
the presentation is the reduction `TauCeti.LinearMap.piSplitAtQuot` of the exponent vectors: the
element `∏ x, x_x ^ (u x)` of `G^{ab}` is sent to the class of `u`. -/
@[simp]
theorem oneRelatorAbelianizationEquiv_abelianizationHom_ofAdd [Fintype X] (u : X → ℤ_[p]) :
    oneRelatorAbelianizationEquiv r x₀ w hw q hr (abelianizationHom {r} (ofAdd u)) =
      ofAdd (LinearMap.piSplitAtQuot x₀ w hw q u) := by
  rw [oneRelatorAbelianizationEquiv_apply, toSplitQuot_abelianizationHom,
    piSplitAtQuotMultiplicative_ofAdd]

/-- The abelianization isomorphism of a one-relator group sends the class of the generator at
`x ≠ x₀` to the coordinate vector at `x`. -/
@[simp]
theorem oneRelatorAbelianizationEquiv_mk_of_ne [DecidableEq X] {x : X} (hx : x ≠ x₀) :
    oneRelatorAbelianizationEquiv r x₀ w hw q hr
        ((of p {r} x : presentedProP p X {r}) : TopologicalAbelianization (presentedProP p X {r})) =
      ofAdd (Pi.single ⟨x, hx⟩ 1, 0) := by
  rw [← mk_of, oneRelatorAbelianizationEquiv_mk, freeProP.exponentSum_of, toAdd_ofAdd,
    LinearMap.piSplitAtQuot_single_of_ne x₀ w hw q hx]

/-- The abelianization isomorphism of a one-relator group sends the class of the generator at `x₀`
to `(-w, 1)`. -/
@[simp]
theorem oneRelatorAbelianizationEquiv_mk_of_self :
    oneRelatorAbelianizationEquiv r x₀ w hw q hr
        ((of p {r} x₀ : presentedProP p X {r}) :
          TopologicalAbelianization (presentedProP p X {r})) =
      ofAdd (fun x : {x // x ≠ x₀} ↦ -w x, Submodule.Quotient.mk 1) := by
  classical
  rw [← mk_of, oneRelatorAbelianizationEquiv_mk, freeProP.exponentSum_of, toAdd_ofAdd,
    LinearMap.piSplitAtQuot_single_self x₀ w hw q]

/-- The inverse of the abelianization isomorphism of a one-relator group: the class of `(a, b)` is
sent to `∏ x, x_x ^ (u x)` for `u` the vector with coordinates `a` away from `x₀` and `b` along
`w`, that is `u = (piSplitAt x₀ w).symm (a, b)`. -/
theorem oneRelatorAbelianizationEquiv_symm_ofAdd_mk [Fintype X] (a : {x // x ≠ x₀} → ℤ_[p])
    (b : ℤ_[p]) :
    (oneRelatorAbelianizationEquiv r x₀ w hw q hr).symm
        (ofAdd (a, (Submodule.Quotient.mk b : ℤ_[p] ⧸ Ideal.span {q}))) =
      abelianizationHom {r} (ofAdd ((LinearEquiv.piSplitAt x₀ w hw).symm (a, b))) := by
  rw [ContinuousMulEquiv.symm_apply_eq, oneRelatorAbelianizationEquiv_abelianizationHom_ofAdd,
    LinearMap.piSplitAtQuot_piSplitAt_symm]

include hw hr in
/-- **The torsion-free case of the structure theorem.** The coordinate `q` of the exponent vector
`exponentSum r = q • w`, `w x₀ = 1`, of the relator vanishes exactly when `r` lies in the closed
commutator subgroup of the free pro-`p` group; then the factor `ℤ_p ⧸ q ℤ_p` of
`oneRelatorAbelianizationEquiv` is `ℤ_p` and `G^{ab} ≅ ℤ_p^X` is torsion-free. -/
theorem oneRelator_q_eq_zero_iff_mem_topologicalClosure_commutator :
    q = 0 ↔ r ∈ (commutator (freeProP p X)).topologicalClosure := by
  rw [← freeProP.exponentSum_eq_one_iff, ← toAdd_eq_zero, hr]
  constructor
  · rintro rfl
    exact zero_smul _ _
  · intro h
    have := congr_fun h x₀
    rwa [Pi.smul_apply, hw, smul_eq_mul, mul_one, Pi.zero_apply] at this

end OneRelator

/-- **Existence form of the abelianization structure theorem.** For a one-relator pro-`p` group
`G = ⟨X ∣ r⟩` on a finite nonempty type, some coordinate `x₀` of the exponent vector `v` of `r`
divides all the others, and `G^{ab} ≅ ℤ_p^{X ∖ {x₀}} × ℤ_p ⧸ v x₀ ℤ_p`. -/
theorem exists_nonempty_oneRelatorAbelianizationEquiv [Finite X] [Nonempty X]
    (r : freeProP p X) :
    ∃ x₀ : X, (∀ x, (freeProP.exponentSum p X r).toAdd x₀ ∣ (freeProP.exponentSum p X r).toAdd x) ∧
      Nonempty (TopologicalAbelianization (presentedProP p X {r}) ≃ₜ*
        Multiplicative (({x // x ≠ x₀} → ℤ_[p]) ×
          (ℤ_[p] ⧸ Ideal.span {(freeProP.exponentSum p X r).toAdd x₀}))) := by
  obtain ⟨x₀, hx₀⟩ := PreValuationRing.exists_forall_dvd (freeProP.exponentSum p X r).toAdd
  obtain ⟨w, hw, hv⟩ := exists_eq_smul_of_forall_dvd hx₀
  exact ⟨x₀, hx₀, ⟨oneRelatorAbelianizationEquiv r x₀ w hw _ hv⟩⟩

end presentedProP

end TauCeti
