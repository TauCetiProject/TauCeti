/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.LSPath.Distinguished
import TauCeti.LinearAlgebra.RootSystem.Reduced
import TauCeti.LinearAlgebra.RootSystem.Weyl.Orbit.Ray
import TauCeti.RepresentationTheory.LSPath.OrbitStable
import TauCeti.RepresentationTheory.LSPath.Realization

/-!
# Central transport of Lakshmibai–Seshadri paths

Let `χ` be a weight killed by the simple coroots, such as a central character of a reductive root
datum. Then `χ` is fixed by the Weyl group, so `w (λ + χ) = w λ + χ`, and adding `χ` changes
neither the walls through `λ` nor the bonds `b_λ(x, y)` of the covers of `W / W_λ`
(`RootPairing.wallIndices_add_of_forall_coroot'_eq_zero`, `TauCeti.reflectionBond_smul_add`).
So a Lakshmibai–Seshadri path `(τ; a)` of shape `λ` is, with the same directions and the same
breaks, a Lakshmibai–Seshadri path of shape `λ + χ`. This is the bijection
`TauCeti.LSPath.centralTransport χ : LSPath P b λ ≃ LSPath P b (λ + χ)`, and more generally
`TauCeti.LSPath.centralTransportOfEq` between any two shapes satisfying `λ + χ = λ'`.

On the realized paths it adds the linear path `t ↦ t χ`: the segment `(a_{j+1} - a_j) τ_j λ` of
duration `a_{j+1} - a_j` becomes `(a_{j+1} - a_j) τ_j (λ + χ)`. Adding `t ↦ t χ` is not well
defined on reparametrization classes of paths (`TauCeti.PLPath.not_exists_shiftTimed_on_paths`);
it is applied here to the presentation by directions and breaks, whose velocities are the orbit
weights. For dominant `λ` and a realization `f` injective on `W λ`, this presentation is
distinguished for the realized orbit (`TauCeti.LSPath.isDistinguished_timed`); if moreover no two
distinct points of the realized orbit lie on a common ray — in particular whenever linear forms
realize the simple coroots — the transport is the central shift
`TauCeti.PLPath.shiftDistinguished` (`TauCeti.LSPath.toPLPath_centralTransport`,
`TauCeti.LSPath.toPLPath_centralTransport_of_coroot'`).

The transport moves the endpoint by `χ`, keeps the minimum height of every form killing `χ` (in
particular of the simple coroots, whose minimum heights govern the root operators), sends the
straight path of shape `λ` to that of shape `λ + χ`, and composes additively in `χ`, with the
transport by `0` equal to the identity and the transport by `-χ` inverting that by `χ`.

## Main definitions

* `TauCeti.LSPath.centralTransportOfEq` and `TauCeti.LSPath.centralTransport`: the bijection
  `LSPath P b λ ≃ LSPath P b λ'` when `λ + χ = λ'` for a weight `χ` killed by the simple coroots,
  and its specialization to `λ' = λ + χ`.

## Main results

* `TauCeti.LSPath.timed_centralTransport`: the transported presentation adds `t ↦ t χ` to the
  presentation by directions and breaks.
* `TauCeti.LSPath.toPLPath_centralTransport` and
  `TauCeti.LSPath.toPLPath_centralTransport_of_coroot'`: **for dominant `λ`, the transported path is
  the central shift of the original path along `W λ`.**
* `TauCeti.LSPath.endpoint_toPLPath_centralTransport` and
  `TauCeti.LSPath.minHeight_toPLPath_centralTransport`: the endpoint moves by `χ` and the minimum
  height of a form killing `χ` is unchanged.
* `TauCeti.LSPath.toPLPath_centralTransport_centralTransport`,
  `TauCeti.LSPath.toPLPath_centralTransport_zero` and
  `TauCeti.LSPath.toPLPath_centralTransport_neg`: on realized paths the transports compose
  additively, the transport by `0` is the identity, and the transport by `-χ` inverts the
  transport by `χ`.
* `TauCeti.LSPath.lower_toPLPath_centralTransport_of_coroot'`,
  `TauCeti.LSPath.raise_toPLPath_centralTransport_of_coroot'`: Littelmann's lowering and raising
  operators commute with central transport on realized LS paths of dominant shape.

## References

* P. Littelmann, *A Littlewood–Richardson rule for symmetrizable Kac–Moody algebras*, Invent.
  Math. 116 (1994), 329--346, Section 4.
* P. Littelmann, *Paths and root operators in representation theory*, Ann. of Math. 142 (1995),
  499--525, Section 4.
-/

public section

universe u w x

namespace TauCeti

open RootPairing

variable {ι : Type u} {M : Type w} {N : Type x} [AddCommGroup M] [AddCommGroup N]
  {P : RootPairing ι ℤ M N} {b : P.Base} [Finite ι] [P.IsReduced]

namespace LSPath

/-- An LS encoding of shape `λ` is one of shape `λ'` when the two weights have the same walls and
the same bonds between their orbit weights: the directions and breaks are unchanged. -/
private def transport {lam lam' : M} (hJ : P.wallIndices b lam = P.wallIndices b lam')
    (hbond : ∀ x y : P.weylGroup,
      P.reflectionBond b (x • lam') (y • lam') = P.reflectionBond b (x • lam) (y • lam))
    (π : LSPath P b lam) : LSPath P b lam' where
  length := π.length
  dir j := ⟨(π.dir j).1, hJ ▸ (π.dir j).2⟩
  time := π.time
  time_zero := π.time_zero
  time_last := π.time_last
  strictMono_time := π.strictMono_time
  dir_succ_ne j h := by
    have hval := congrArg Subtype.val h
    exact π.dir_succ_ne j (Subtype.ext hval)
  exists_isAChain j := by
    obtain ⟨C, hhead, hlast, hC⟩ := π.exists_isAChain j
    have hcov (y x : P.weylGroup)
        (h : (weylCoxeterSystem P b).MinimalCosetRepCovBy (P.wallIndices b lam) y x) :
        (weylCoxeterSystem P b).MinimalCosetRepCovBy (P.wallIndices b lam') y x :=
      hJ ▸ h
    refine ⟨(C.map ⟨fun x ↦ ⟨x.1, hJ ▸ x.2⟩, fun h ↦ hcov _ _ h⟩ :
      (weylCoxeterSystem P b).MinimalCosetRepChain (P.wallIndices b lam')),
      by rw [RelSeries.head_map, hhead]; rfl, by rw [RelSeries.last_map, hlast]; rfl, ?_⟩
    rw [isAChain_iff_den_dvd_bondGcd, dvd_bondGcd_iff] at hC ⊢
    intro i
    rw [hbond]
    exact hC i

/-- **Central transport of Lakshmibai–Seshadri paths between shapes differing by a central weight.**
When `λ + χ = λ'` for a weight `χ` killed by the simple coroots, a Lakshmibai–Seshadri path of
shape `λ` is, with the same directions and breaks, one of shape `λ'`. -/
noncomputable def centralTransportOfEq {lam lam' : M} (χ : M)
    (hχ : ∀ i ∈ b.support, P.coroot' i χ = 0) (h : lam + χ = lam') :
    LSPath P b lam ≃ LSPath P b lam' where
  toFun := transport (h ▸ (wallIndices_add_of_forall_coroot'_eq_zero hχ).symm)
    fun x y ↦ h ▸ reflectionBond_smul_add hχ lam x y
  invFun := transport (h ▸ wallIndices_add_of_forall_coroot'_eq_zero hχ)
    fun x y ↦ h ▸ (reflectionBond_smul_add hχ lam x y).symm
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
theorem centralTransportOfEq_zero {lam : M}
    (h0 : ∀ i ∈ b.support, P.coroot' i (0 : M) = 0) (h : lam + 0 = lam) :
    centralTransportOfEq (0 : M) h0 h = Equiv.refl (LSPath P b lam) :=
  (rfl)

theorem centralTransportOfEq_zero_apply {lam : M}
    (h0 : ∀ i ∈ b.support, P.coroot' i (0 : M) = 0) (h : lam + 0 = lam) (π : LSPath P b lam) :
    centralTransportOfEq (0 : M) h0 h π = π :=
  (rfl)

@[simp]
theorem centralTransportOfEq_trans {lam₁ lam₂ lam₃ χ ψ : M}
    (hχ : ∀ i ∈ b.support, P.coroot' i χ = 0) (h₁ : lam₁ + χ = lam₂)
    (hψ : ∀ i ∈ b.support, P.coroot' i ψ = 0) (h₂ : lam₂ + ψ = lam₃) :
    (centralTransportOfEq χ hχ h₁).trans (centralTransportOfEq ψ hψ h₂) =
      centralTransportOfEq (χ + ψ) (fun i hi ↦ by rw [map_add, hχ i hi, hψ i hi, add_zero])
        (by rw [← add_assoc, h₁, h₂]) :=
  (rfl)

@[simp]
theorem centralTransportOfEq_trans_apply {lam₁ lam₂ lam₃ χ ψ : M}
    (hχ : ∀ i ∈ b.support, P.coroot' i χ = 0) (h₁ : lam₁ + χ = lam₂)
    (hψ : ∀ i ∈ b.support, P.coroot' i ψ = 0) (h₂ : lam₂ + ψ = lam₃) (π : LSPath P b lam₁) :
    centralTransportOfEq ψ hψ h₂ (centralTransportOfEq χ hχ h₁ π) =
      centralTransportOfEq (χ + ψ) (fun i hi ↦ by rw [map_add, hχ i hi, hψ i hi, add_zero])
        (by rw [← add_assoc, h₁, h₂]) π :=
  (rfl)

@[simp]
theorem centralTransportOfEq_symm {lam lam' χ : M}
    (hχ : ∀ i ∈ b.support, P.coroot' i χ = 0) (h : lam + χ = lam') :
    (centralTransportOfEq χ hχ h).symm =
      centralTransportOfEq (-χ) (fun i hi ↦ by rw [map_neg, hχ i hi, neg_zero])
        (by rw [← h, add_neg_cancel_right]) :=
  (rfl)

variable (χ : M) (hχ : ∀ i ∈ b.support, P.coroot' i χ = 0) {lam : M}

/-- **Central transport of Lakshmibai–Seshadri paths.** For a weight `χ` killed by the simple
coroots, a Lakshmibai–Seshadri path of shape `λ` is, with the same directions and breaks, one of
shape `λ + χ`: adding `χ` changes neither the walls through `λ` nor the bonds of `W / W_λ`. On the
realized paths this adds the linear path `t ↦ t χ` to the presentation by directions and breaks
(`TauCeti.LSPath.timed_centralTransport`). -/
noncomputable def centralTransport : LSPath P b lam ≃ LSPath P b (lam + χ) :=
  centralTransportOfEq χ hχ rfl

theorem centralTransport_eq_centralTransportOfEq :
    centralTransport (P := P) (b := b) (lam := lam) χ hχ = centralTransportOfEq χ hχ rfl :=
  (rfl)

variable (π : LSPath P b lam)

@[simp]
theorem length_centralTransport : (centralTransport χ hχ π).length = π.length :=
  (rfl)

/-- The central transport keeps the directions of an LS path. -/
@[simp]
theorem dir_centralTransport (j : Fin ((centralTransport χ hχ π).length + 1)) :
    ((centralTransport χ hχ π).dir j).1 = (π.dir (j.cast (by rw [length_centralTransport]))).1 :=
  (rfl)

/-- The central transport keeps the breaks of an LS path. -/
@[simp]
theorem time_centralTransport (k : Fin ((centralTransport χ hχ π).length + 2)) :
    (centralTransport χ hχ π).time k = π.time (k.cast (by rw [length_centralTransport])) :=
  (rfl)

@[simp]
theorem duration_centralTransport (j : Fin ((centralTransport χ hχ π).length + 1)) :
    (centralTransport χ hχ π).duration j =
      π.duration (j.cast (by rw [length_centralTransport])) := by
  simp [duration_def]

@[simp]
theorem length_centralTransport_symm (π : LSPath P b (lam + χ)) :
    ((centralTransport χ hχ).symm π).length = π.length :=
  (rfl)

@[simp]
theorem dir_centralTransport_symm (π : LSPath P b (lam + χ))
    (j : Fin (((centralTransport χ hχ).symm π).length + 1)) :
    (((centralTransport χ hχ).symm π).dir j).1 =
      (π.dir (j.cast (by rw [length_centralTransport_symm]))).1 :=
  (rfl)

@[simp]
theorem time_centralTransport_symm (π : LSPath P b (lam + χ))
    (k : Fin (((centralTransport χ hχ).symm π).length + 2)) :
    ((centralTransport χ hχ).symm π).time k =
      π.time (k.cast (by rw [length_centralTransport_symm])) :=
  (rfl)

@[simp]
theorem duration_centralTransport_symm (π : LSPath P b (lam + χ))
    (j : Fin (((centralTransport χ hχ).symm π).length + 1)) :
    ((centralTransport χ hχ).symm π).duration j =
      π.duration (j.cast (by rw [length_centralTransport_symm])) := by
  simp [duration_def]

variable (lam) in
/-- The central transport of the straight path of shape `λ` is the straight path of shape
`λ + χ`. -/
@[simp]
theorem centralTransport_straight : centralTransport χ hχ (straight lam) = straight (lam + χ) := by
  apply LSPath.ext
  · apply List.ext_get
    · simp
    · intro n h₁ h₂
      simp only [List.get_eq_getElem, List.getElem_ofFn]
      exact Subtype.ext (by simp)
  · apply List.ext_get
    · simp
    · intro n h₁ h₂
      simp

@[simp]
theorem centralTransportOfEq_straight {lam' : M} (h : lam + χ = lam') :
    centralTransportOfEq χ hχ h (straight lam) = straight lam' := by
  subst h
  exact centralTransport_straight χ hχ lam

variable (𝕜 : Type*) {V : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [AddCommGroup V] [Module 𝕜 V] (f : M →+ V)

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- **The central transport adds `t ↦ t χ` to the presentation by directions and breaks**: the
segment `(a_{j+1} - a_j) τ_j λ` becomes `(a_{j+1} - a_j) τ_j (λ + χ) = (a_{j+1} - a_j) (τ_j λ + χ)`.
-/
@[simp]
theorem timed_centralTransport :
    (centralTransport χ hχ π).timed 𝕜 f = PLPath.shiftTimed (f χ) (π.timed 𝕜 f) := by
  rw [timed_def, timed_def, PLPath.shiftTimed_def, List.map_ofFn,
    List.ofFn_congr (congrArg (· + 1) (length_centralTransport χ hχ π))]
  congr 1
  funext j
  simp [smul_eq_self_of_forall_coroot'_eq_zero b hχ, smul_add]

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
@[simp]
theorem timed_centralTransportOfEq {lam' : M} (h : lam + χ = lam') :
    (centralTransportOfEq χ hχ h π).timed 𝕜 f = PLPath.shiftTimed (f χ) (π.timed 𝕜 f) := by
  subst h
  exact timed_centralTransport χ hχ π 𝕜 f

/-- The realized path of the central transport is presented by adding `t ↦ t χ` to the
presentation by directions and breaks. -/
theorem toPLPath_centralTransport_eq_ofSegments :
    (centralTransport χ hχ π).toPLPath 𝕜 f =
      PLPath.ofSegments 𝕜 ((PLPath.shiftTimed (f χ) (π.timed 𝕜 f)).map Prod.snd) := by
  rw [toPLPath_def, timed_centralTransport]

/-- The central transport moves the endpoint of an LS path by `χ`. -/
@[simp]
theorem endpoint_toPLPath_centralTransport :
    ((centralTransport χ hχ π).toPLPath 𝕜 f).endpoint = (π.toPLPath 𝕜 f).endpoint + f χ := by
  rw [toPLPath_centralTransport_eq_ofSegments, PLPath.endpoint_ofSegments_shiftTimed,
    duration_timed, one_smul, toPLPath_def]

@[simp]
theorem endpoint_toPLPath_centralTransportOfEq {lam' : M} (h : lam + χ = lam') :
    ((centralTransportOfEq χ hχ h π).toPLPath 𝕜 f).endpoint = (π.toPLPath 𝕜 f).endpoint + f χ := by
  subst h
  exact endpoint_toPLPath_centralTransport χ hχ π 𝕜 f

/-- A linear form killing `χ` has the same minimum height on an LS path and on its central
transport. This applies to the simple coroots, whose minimum heights govern the root operators. -/
@[simp]
theorem minHeight_toPLPath_centralTransport {g : Module.Dual 𝕜 V} (hg : g (f χ) = 0) :
    ((centralTransport χ hχ π).toPLPath 𝕜 f).minHeight g = (π.toPLPath 𝕜 f).minHeight g := by
  rw [toPLPath_centralTransport_eq_ofSegments, PLPath.minHeight_ofSegments_shiftTimed hg,
    toPLPath_def]

@[simp]
theorem minHeight_toPLPath_centralTransportOfEq {lam' : M} (h : lam + χ = lam')
    {g : Module.Dual 𝕜 V} (hg : g (f χ) = 0) :
    ((centralTransportOfEq χ hχ h π).toPLPath 𝕜 f).minHeight g = (π.toPLPath 𝕜 f).minHeight g := by
  subst h
  exact minHeight_toPLPath_centralTransport χ hχ π 𝕜 f hg

/-- **The central transport is the central shift of the realized path.** For dominant `λ`, a
realization `f` injective on `W λ` and a realized orbit with no two distinct points on a common ray,
the path of the central transport of `π` is obtained from the path of `π` by adding `t ↦ t χ` to
its distinguished presentation for the realized orbit `W λ`. -/
theorem toPLPath_centralTransport (hlam : lam ∈ dominantChamber P b)
    (hf : Set.InjOn f (Set.range fun w : P.weylGroup ↦ w • lam))
    (hS : (Set.range fun w : P.weylGroup ↦ f (w • lam)).Pairwise fun u v ↦ ¬ SameRay 𝕜 u v) :
    (centralTransport χ hχ π).toPLPath 𝕜 f =
      PLPath.shiftDistinguished (Set.range fun w : P.weylGroup ↦ f (w • lam)) (f χ)
        (π.toPLPath 𝕜 f) := by
  have := P.flip_isReduced
  rw [toPLPath_centralTransport_eq_ofSegments, toPLPath_def,
    PLPath.shiftDistinguished_ofSegments (π.isDistinguished_timed 𝕜 f hlam hf) hS]

/-- When linear forms on `V` realize the simple coroots, the central transport of an LS path of
dominant shape `λ` acts on its realized path as `TauCeti.PLPath.shiftDistinguished` along the
realized orbit `W λ`. -/
theorem toPLPath_centralTransport_of_coroot' (hlam : lam ∈ dominantChamber P b)
    {F : b.support → Module.Dual 𝕜 V}
    (hF : ∀ (i : b.support) m, F i (f m) = (P.coroot' i m : 𝕜)) :
    (centralTransport χ hχ π).toPLPath 𝕜 f =
      PLPath.shiftDistinguished (Set.range fun w : P.weylGroup ↦ f (w • lam)) (f χ)
        (π.toPLPath 𝕜 f) :=
  toPLPath_centralTransport χ hχ π 𝕜 f hlam (injOn_range_smul_of_coroot' hF lam)
    (pairwise_not_sameRay_range_smul hF lam)

theorem toPLPath_centralTransportOfEq_of_coroot' {lam' : M} (h : lam + χ = lam')
    (hlam : lam ∈ dominantChamber P b) {F : b.support → Module.Dual 𝕜 V}
    (hF : ∀ (i : b.support) m, F i (f m) = (P.coroot' i m : 𝕜)) :
    (centralTransportOfEq χ hχ h π).toPLPath 𝕜 f =
      PLPath.shiftDistinguished (Set.range fun w : P.weylGroup ↦ f (w • lam)) (f χ)
        (π.toPLPath 𝕜 f) := by
  subst h
  exact toPLPath_centralTransport_of_coroot' χ hχ π 𝕜 f hlam hF

/-- **Lowering commutes with central transport of realized LS paths.** -/
theorem lower_toPLPath_centralTransport_of_coroot' (hlam : lam ∈ dominantChamber P b)
    {F : b.support → Module.Dual 𝕜 V}
    (hF : ∀ (i : b.support) m, F i (f m) = (P.coroot' i m : 𝕜)) (i : b.support) :
    PLPath.lower (F i) (f (P.root i)) ((centralTransport χ hχ π).toPLPath 𝕜 f) =
      (PLPath.lower (F i) (f (P.root i)) (π.toPLPath 𝕜 f)).map
        (PLPath.shiftDistinguished (Set.range fun w : P.weylGroup ↦ f (w • lam)) (f χ)) := by
  have hS := P.mapsTo_preReflection_image_orbit_weylGroup i.1 (hF i) lam
  rw [MulAction.orbit, ← Set.range_comp] at hS
  have hFχ : F i (f χ) = 0 := by rw [hF i χ, hχ i.1 i.2, Int.cast_zero]
  rw [toPLPath_centralTransport_of_coroot' χ hχ π 𝕜 f hlam hF]
  exact PLPath.lower_shiftDistinguished (π.hasDistinguished_toPLPath 𝕜 f) hS
    (pairwise_not_sameRay_range_smul hF lam) hFχ

/-- **Raising commutes with central transport of realized LS paths.** -/
theorem raise_toPLPath_centralTransport_of_coroot' (hlam : lam ∈ dominantChamber P b)
    {F : b.support → Module.Dual 𝕜 V}
    (hF : ∀ (i : b.support) m, F i (f m) = (P.coroot' i m : 𝕜)) (i : b.support) :
    PLPath.raise (F i) (f (P.root i)) ((centralTransport χ hχ π).toPLPath 𝕜 f) =
      (PLPath.raise (F i) (f (P.root i)) (π.toPLPath 𝕜 f)).map
        (PLPath.shiftDistinguished (Set.range fun w : P.weylGroup ↦ f (w • lam)) (f χ)) := by
  have hS := P.mapsTo_preReflection_image_orbit_weylGroup i.1 (hF i) lam
  rw [MulAction.orbit, ← Set.range_comp] at hS
  have hFχ : F i (f χ) = 0 := by rw [hF i χ, hχ i.1 i.2, Int.cast_zero]
  rw [toPLPath_centralTransport_of_coroot' χ hχ π 𝕜 f hlam hF]
  exact PLPath.raise_shiftDistinguished (π.hasDistinguished_toPLPath 𝕜 f) hS
    (pairwise_not_sameRay_range_smul hF lam) hFχ

theorem lower_toPLPath_centralTransportOfEq_of_coroot' {lam' : M} (h : lam + χ = lam')
    (hlam : lam ∈ dominantChamber P b) {F : b.support → Module.Dual 𝕜 V}
    (hF : ∀ (i : b.support) m, F i (f m) = (P.coroot' i m : 𝕜)) (i : b.support) :
    PLPath.lower (F i) (f (P.root i)) ((centralTransportOfEq χ hχ h π).toPLPath 𝕜 f) =
      (PLPath.lower (F i) (f (P.root i)) (π.toPLPath 𝕜 f)).map
        (PLPath.shiftDistinguished (Set.range fun w : P.weylGroup ↦ f (w • lam)) (f χ)) := by
  subst h
  exact lower_toPLPath_centralTransport_of_coroot' χ hχ π 𝕜 f hlam hF i

theorem raise_toPLPath_centralTransportOfEq_of_coroot' {lam' : M} (h : lam + χ = lam')
    (hlam : lam ∈ dominantChamber P b) {F : b.support → Module.Dual 𝕜 V}
    (hF : ∀ (i : b.support) m, F i (f m) = (P.coroot' i m : 𝕜)) (i : b.support) :
    PLPath.raise (F i) (f (P.root i)) ((centralTransportOfEq χ hχ h π).toPLPath 𝕜 f) =
      (PLPath.raise (F i) (f (P.root i)) (π.toPLPath 𝕜 f)).map
        (PLPath.shiftDistinguished (Set.range fun w : P.weylGroup ↦ f (w • lam)) (f χ)) := by
  subst h
  exact raise_toPLPath_centralTransport_of_coroot' χ hχ π 𝕜 f hlam hF i

/-- **Central transports compose additively** on realized paths: transporting by `χ` and then by
`ψ` gives the same path as transporting by `χ + ψ`. -/
@[simp]
theorem toPLPath_centralTransport_centralTransport {ψ : M}
    (hψ : ∀ i ∈ b.support, P.coroot' i ψ = 0) :
    (centralTransport ψ hψ (centralTransport χ hχ π)).toPLPath 𝕜 f =
      (centralTransport (χ + ψ) (fun i hi ↦ by rw [map_add, hχ i hi, hψ i hi, add_zero]) π).toPLPath
        𝕜 f := by
  simp [toPLPath_def, PLPath.shiftTimed_shiftTimed]

/-- The central transport by `0` does not change the realized path. -/
@[simp]
theorem toPLPath_centralTransport_zero :
    (centralTransport (0 : M) (fun _ _ ↦ map_zero _) π).toPLPath 𝕜 f = π.toPLPath 𝕜 f := by
  simp [toPLPath_def, PLPath.shiftTimed_zero]

/-- **The inverse of a central transport.** On realized paths, the inverse of the central
transport by `χ` is the central transport by `-χ`. -/
theorem toPLPath_centralTransport_neg (π : LSPath P b (lam + χ)) :
    (centralTransport (-χ) (fun i hi ↦ by rw [map_neg, hχ i hi, neg_zero]) π).toPLPath 𝕜 f =
      ((centralTransport χ hχ).symm π).toPLPath 𝕜 f := by
  conv_lhs => rw [← (centralTransport χ hχ).apply_symm_apply π]
  rw [toPLPath_centralTransport_centralTransport]
  simp [toPLPath_def, PLPath.shiftTimed_zero]

end LSPath

end TauCeti
