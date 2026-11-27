/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Contact.Interpolation
public import TauCeti.Geometry.Manifold.SmoothEmbedding.Basic
import TauCeti.Geometry.Contact.Pullback
import TauCeti.Geometry.Manifold.DifferentialForm.Opens
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Constructions
import TauCeti.Geometry.Manifold.DifferentialForm.Proportional
import TauCeti.Geometry.Manifold.DifferentialForm.Wedge.Leibniz
import TauCeti.Geometry.Manifold.TubularNeighborhood.PrescribedDifferential

/-!
# Contact neighbourhood germs with prescribed first-order data

Let `α` be a one-form on a manifold `M` and `β` a one-form on a manifold `N`. This file shows that
a contactomorphism between neighbourhoods of two submanifolds can be built from its first-order
data along them, without any isotropy or compactness assumption.

**Correcting a partial diffeomorphism.** Let `Ψ` be a partial diffeomorphism from `M` to `N`, and
let `S` be a set of points of its source at which `α` is contact. Suppose that at every `x ∈ S`
the differential of `Ψ` carries the first-order data of `β` to those of `α` up to a positive
factor `c x`:

`β(dΨ v) = c x α(v)` for all `v`, and `dβ(dΨ v, dΨ w) = c x dα(v, w)` for `v, w ∈ ker α_x`.

Then `Ψ` can be corrected to a partial diffeomorphism `φ` which agrees with `Ψ` on `S` and pulls
`β` back to a positive multiple of `α` on its source, so that `φ` is a coorientation-preserving
contactomorphism of neighbourhoods of `S` and `Ψ(S)`
(`PartialDiffeomorph.exists_eqOn_mpullback_eq_smul`). On the source of `Ψ` the forms `α` and
`Ψ^* β` agree to first order on the contact hyperplanes along `S` up to the factor `c`, so relative
Gray stability for such forms
(`TauCeti.SmoothForm.exists_partialDiffeomorph_mpullback_eq_smul_of_eq_smul`) gives a partial
diffeomorphism `Θ` fixing `S` with `Θ^* Ψ^* β` a positive multiple of `α`, and `φ = Ψ ∘ Θ`.
Conversely, if a partial diffeomorphism pulls `β` back to `h α` for a pointwise multiplier `h`, then
at each point where `α` is contact its differential satisfies the second condition with the factor
`h` (`PartialDiffeomorph.mextDeriv_mfderiv_eq_mul_of_mpullback_eq_smul`): the multiplier is smooth
there, and `d(h α) = dh ∧ α + h dα` restricts to `h dα` on `ker α`.

**Prescribed first-order data along an embedding.** Let `i : Q → M` be a smooth embedding and
`g : Q → N` a smooth map inducing the topology of `Q`, and let `A q : T_{i q} M → T_{g q} N` be
linear isomorphisms, smooth in tangent coordinates, extending the differential of `g` along `i`,
`A q ∘ d i_q = d g_q`. If `α` is contact along `i(Q)` and, for a positive function `c` on `Q`,

`β(A q v) = c q α(v)` for all `v`, and `dβ(A q v, A q w) = c q dα(v, w)` for `v, w ∈ ker α_{i q}`,

then there is a partial diffeomorphism `φ` from a neighbourhood of `i(Q)` with `φ ∘ i = g` which
pulls `β` back to a positive multiple of `α` on its source
(`TauCeti.SmoothEmbedding.exists_partialDiffeomorph_comp_eq_mpullback_eq_smul`). The data `A` are
first realized as the differential of a partial diffeomorphism `Ψ` with `Ψ ∘ i = g`
(`TauCeti.SmoothEmbedding.exists_partialDiffeomorph_mfderiv_eq`), which is then corrected as above.
The factor `c` is the identification of the contact lines `TM / ker α` and `TN / ker β` along the
submanifolds read in the trivializations given by `α` and `β`, and the second condition says that
`A` is conformally symplectic for the Levi forms with respect to it. This is the step of the
isotropic neighbourhood theorem that turns an identification of the full first-order data along
the submanifolds into a contactomorphism of neighbourhood germs. Neither `M`, `N` nor `Q` need be
compact, and `i(Q)` need not be isotropic. These conditions are also necessary, with
`A q = dφ_{i q}` and `c q` the multiplier at `i q`, so they characterize the maps `g` that extend to
such a `φ`
(`TauCeti.SmoothEmbedding.exists_partialDiffeomorph_comp_eq_mpullback_eq_smul_iff`). The
contactomorphism `φ` is not claimed to have differential `A` along `i(Q)`.

## Main results

* `PartialDiffeomorph.exists_eqOn_mpullback_eq_smul`: a partial diffeomorphism whose differential
  carries the first-order contact data of `β` to those of `α` along `S`, up to a positive factor,
  agrees on `S` with a coorientation-preserving contactomorphism of neighbourhoods of `S`.
* `PartialDiffeomorph.mextDeriv_mfderiv_eq_mul_of_mpullback_eq_smul`: a partial diffeomorphism
  pulling `β` back to a multiple of `α` is conformally symplectic for the Levi forms.
* `TauCeti.SmoothEmbedding.exists_partialDiffeomorph_comp_eq_mpullback_eq_smul`: an identification
  of the first-order contact data along an embedded submanifold, over a map `g`, extends `g` to a
  coorientation-preserving contactomorphism of neighbourhoods.
* `TauCeti.SmoothEmbedding.exists_partialDiffeomorph_comp_eq_mpullback_eq_smul_iff`: the maps `g`
  admitting such an extension are characterized by these first-order data.

## References

* H. Geiges, *An Introduction to Contact Topology*, Cambridge University Press, 2008,
  Theorem 2.2.2 (Gray stability) and Section 2.5 (neighbourhood theorems; the isotropic
  neighbourhood theorem compares two contact structures after identifying their first-order data
  along the submanifold).
-/

public section

noncomputable section

open Set TopologicalSpace
open scoped Manifold Topology ContDiff

variable {E F H G M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace H] [TopologicalSpace G] {I : ModelWithCorners ℝ E H}
  {K : ModelWithCorners ℝ F G} [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace N] [ChartedSpace G N]

variable [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [T2Space M]
  [IsManifold K ∞ N] {α : TauCeti.SmoothForm I M ℝ 1} {β : TauCeti.SmoothForm K N ℝ 1}

namespace PartialDiffeomorph

open TauCeti

/-- **Correcting a partial diffeomorphism to a contactomorphism.** Let `Ψ` be a partial
diffeomorphism from `M` to `N`, with `M` finite-dimensional, boundaryless and Hausdorff, let `S` be
a set of points of its source at which the one-form `α` is contact, and let `c` be positive on `S`.
Suppose that at
every `x ∈ S` the differential of `Ψ` carries the first-order data of the one-form `β` to `c x`
times those of `α`: `β(dΨ v) = c x α(v)` for every tangent vector `v`, and
`dβ(dΨ v, dΨ w) = c x dα(v, w)` for `v` and `w` in `ker α_x`. Then there is a partial
diffeomorphism `φ` from `M` to `N` whose source contains `S`, which agrees with `Ψ` on `S` and
pulls `β` back to a positive multiple of `α` at every point of its source. Neither `S` nor `M` need
be compact. -/
theorem exists_eqOn_mpullback_eq_smul (Ψ : PartialDiffeomorph I K M N ∞) {S : Set M}
    (hS : S ⊆ Ψ.source) {c : M → ℝ} (hα : ∀ x ∈ S, IsContactFormAt α.val x)
    (hc : ∀ x ∈ S, 0 < c x)
    (hβ : ∀ x ∈ S, ∀ v : TangentSpace I x,
      β.val (Ψ x) ![mfderiv I K Ψ x v] = c x * α.val x ![v])
    (hdβ : ∀ x ∈ S, ∀ v ∈ RoughForm.ker α.val x, ∀ w ∈ RoughForm.ker α.val x,
      mextDeriv β.val (Ψ x) ![mfderiv I K Ψ x v, mfderiv I K Ψ x w] =
        c x * mextDeriv α.val x ![v, w]) :
    ∃ φ : PartialDiffeomorph I K M N ∞, S ⊆ φ.source ∧ EqOn φ Ψ S ∧
      ∀ x ∈ φ.source, ∃ h : ℝ, 0 < h ∧ TauCeti.mpullback I K φ β.val x = h • α.val x := by
  -- On the source `U` of `Ψ`, compare the restriction `α₀` of `α` with `α₁ = Ψ^* β`.
  let U : Opens M := ⟨Ψ.source, Ψ.open_source⟩
  have hΨU : ContMDiff I K ∞ (Ψ ∘ (Subtype.val : U → M)) :=
    Ψ.contMDiffOn.comp_contMDiff contMDiff_subtypeVal fun z ↦ z.property
  set α₀ := SmoothForm.mpullback (Subtype.val : U → M) contMDiff_subtypeVal α
  set α₁ := SmoothForm.mpullback _ hΨU β
  have hΨ (z : U) : MDifferentiableAt I K Ψ z := Ψ.mdifferentiableAt (by simp) z.property
  -- As rough forms on `U`, `α₁` is the restriction of the rough form `Ψ^* β` on `M`.
  have hα₁ : α₁.val = mpullback I I (Subtype.val : U → M) (mpullback I K Ψ β.val) := by
    funext z
    rw [SmoothForm.coe_mpullback]
    exact mpullback_comp_at (contMDiff_subtypeVal.mdifferentiableAt one_ne_zero) (hΨ z) β.val
  obtain ⟨Θ, hsrc, htgt, hfix, hΘ⟩ :=
    SmoothForm.exists_partialDiffeomorph_mpullback_eq_smul_of_eq_smul (α₀ := α₀) (α₁ := α₁)
      (K := Subtype.val ⁻¹' S) (c := c ∘ Subtype.val)
      (fun z hz ↦ (SmoothForm.isContactFormAt_mpullback_subtype_val_iff α z).2 (hα z hz))
      (fun z hz ↦ hc z hz)
      (fun z hz ↦ by
        rw [hα₁, mpullback_subtype_val_apply, SmoothForm.coe_mpullback_subtype_val_apply]
        ext u
        have hu : u = ![u 0] := funext fun j ↦ by rw [Subsingleton.elim j 0]; rfl
        rw [hu, mpullback_apply_one, hβ z hz]
        -- Both sides are `c z * α_z (u 0)`, read on the tangent spaces of `U` and of `M`.
        rfl)
      fun z hz v hv w hw ↦ by
        have hα₀ : α₀.val z = α.val z := SmoothForm.coe_mpullback_subtype_val_apply α z
        rw [RoughForm.mem_ker, hα₀] at hv hw
        rw [SmoothForm.mextDeriv_mpullback_apply_two, SmoothForm.mextDeriv_mpullback_apply_two,
          Manifold.mfderiv_comp_subtype_val_apply, Manifold.mfderiv_comp_subtype_val_apply]
        simpa only [Manifold.mfderiv_subtype_val_apply, Function.comp_apply] using
          hdβ z hz v (RoughForm.mem_ker.2 hv) w (RoughForm.mem_ker.2 hw)
  -- Read `Θ` in `M`, and correct `Ψ` to `φ = Ψ ∘ Θ`.
  obtain ⟨Φ, hsrcΦ, -, hfixΦ, hΦ⟩ :=
    exists_partialDiffeomorph_mpullback_apply_eq_of_opens (by simp) (W := U) hS Θ hsrc htgt hfix
  refine ⟨Φ.trans Ψ, fun x hx ↦ ?_, fun x hx ↦ ?_, fun x hx ↦ ?_⟩
  · rw [PartialDiffeomorph.trans_source]
    exact ⟨hsrcΦ hx, by rw [mem_preimage, hfixΦ x hx]; exact hS hx⟩
  · rw [PartialDiffeomorph.coe_trans, Function.comp_apply, hfixΦ x hx]
  · rw [PartialDiffeomorph.trans_source] at hx
    obtain ⟨y, hy, rfl, hΦy⟩ := hΦ x hx.1
    obtain ⟨h, hh, hΘy⟩ := hΘ y hy
    refine ⟨h, hh, ?_⟩
    rw [PartialDiffeomorph.coe_trans,
      mpullback_comp_at (Φ.mdifferentiableAt (by simp) hx.1) (Ψ.mdifferentiableAt (by simp) hx.2),
      hΦy, ← hα₁, hΘy]
    exact congrArg (h • ·) (SmoothForm.coe_mpullback_subtype_val_apply α y)

omit [I.Boundaryless] [T2Space M] in
/-- **The Levi data of a conformal pullback.** Let `φ` be a partial diffeomorphism from `M` to `N`
which pulls `β` back to a multiple of `α` at every point of its source, and let `α` be contact at
a point `x` of the source, where `φ^* β = h α`. Then `dβ(dφ v, dφ w) = h dα(v, w)` for `v` and `w`
in `ker α_x`: the differential of `φ` at `x` is conformally symplectic for the Levi forms, with
the factor `h`. -/
theorem mextDeriv_mfderiv_eq_mul_of_mpullback_eq_smul (φ : PartialDiffeomorph I K M N ∞)
    (hφ : ∀ y ∈ φ.source, ∃ h : ℝ, TauCeti.mpullback I K φ β.val y = h • α.val y) {x : M}
    (hx : x ∈ φ.source) (hαx : IsContactFormAt α.val x) {h : ℝ}
    (hh : TauCeti.mpullback I K φ β.val x = h • α.val x) {v w : TangentSpace I x}
    (hv : v ∈ RoughForm.ker α.val x) (hw : w ∈ RoughForm.ker α.val x) :
    mextDeriv β.val (φ x) ![mfderiv I K φ x v, mfderiv I K φ x w] =
      h * mextDeriv α.val x ![v, w] := by
  -- Work on the open set `W` of points of the source of `φ` at which `α` is contact.
  let W : Opens M := ⟨φ.source ∩ {y | IsContactFormAt α.val y},
    φ.open_source.inter (SmoothForm.isOpen_setOf_isContactFormAt α)⟩
  have hφW : ContMDiff I K ∞ (φ ∘ (Subtype.val : W → M)) :=
    φ.contMDiffOn.comp_contMDiff contMDiff_subtypeVal fun z ↦ z.property.1
  obtain ⟨αW, hαWdef⟩ : ∃ γ : SmoothForm I W ℝ 1,
      γ = SmoothForm.mpullback Subtype.val contMDiff_subtypeVal α := ⟨_, rfl⟩
  obtain ⟨βW, hβWdef⟩ : ∃ γ : SmoothForm I W ℝ 1, γ = SmoothForm.mpullback _ hφW β := ⟨_, rfl⟩
  have hαW (z : W) : αW.val z = α.val z := by
    rw [hαWdef]
    exact SmoothForm.coe_mpullback_subtype_val_apply α z
  have hβW (z : W) : βW.val z = TauCeti.mpullback I K φ β.val z := by
    rw [hβWdef, SmoothForm.coe_mpullback, mpullback_comp_at
      (contMDiff_subtypeVal.mdifferentiableAt one_ne_zero)
      (φ.mdifferentiableAt (by simp) z.property.1), mpullback_subtype_val_apply]
  -- On `W`, `φ^* β` is a smooth multiple `f α` of the nowhere-vanishing form `α`.
  obtain ⟨f, ⟨hf, hfβ⟩, -⟩ := SmoothForm.existsUnique_fun_smul_of_ker_le (α := αW) (β := βW)
    (fun z ↦ by rw [hαW]; exact z.property.2.ne_zero) fun z u hu ↦ by
      obtain ⟨c, hc⟩ := hφ z z.property.1
      have hu' : α.val z ![u] = 0 := by rw [← hαW]; exact RoughForm.mem_ker.1 hu
      -- The values of `βW` and of `c α` at `z` act on the same model space.
      exact RoughForm.mem_ker.2 (by rw [hβW, hc]; exact (congrArg (c * ·) hu').trans (mul_zero c))
  let z₀ : W := ⟨x, hx, hαx⟩
  have hfz₀ : f z₀ = h := by
    have hfh := (hfβ z₀).symm.trans (hβW z₀)
    rw [hαW, hh] at hfh
    exact smul_left_injective ℝ hαx.ne_zero hfh
  -- By the Leibniz rule, `d(f α) = f dα` on `ker α_x`.
  have hLeibniz (a b : TangentSpace I z₀) (ha : αW.val z₀ ![a] = 0) (hb : αW.val z₀ ![b] = 0) :
      mextDeriv βW.val z₀ ![a, b] = h * mextDeriv αW.val z₀ ![a, b] := by
    have hd := mextDeriv_fun_smul_apply ((hf z₀).mdifferentiableAt (by simp))
      (αW.mdifferentiableAt z₀) a b
    rwa [ha, hb, mul_zero, mul_zero, sub_zero, zero_add, hfz₀, ← funext hfβ] at hd
  have hd := hLeibniz v w (by rw [hαW]; exact RoughForm.mem_ker.1 hv)
    (by rw [hαW]; exact RoughForm.mem_ker.1 hw)
  -- Read both exterior derivatives in `M` and `N`.
  have hdβW (a b : TangentSpace I z₀) : mextDeriv βW.val z₀ ![a, b] =
      mextDeriv β.val (φ z₀) ![mfderiv I K φ z₀ a, mfderiv I K φ z₀ b] := by
    rw [hβWdef, SmoothForm.mextDeriv_mpullback_apply_two, Manifold.mfderiv_comp_subtype_val_apply,
      Manifold.mfderiv_comp_subtype_val_apply]
    rfl
  have hdαW (a b : TangentSpace I z₀) :
      mextDeriv αW.val z₀ ![a, b] = mextDeriv α.val z₀ ![a, b] := by
    rw [hαWdef, SmoothForm.mextDeriv_mpullback_apply_two, Manifold.mfderiv_subtype_val_apply,
      Manifold.mfderiv_subtype_val_apply]
  -- The base points `z₀` of `W` and `x` of `M` agree, and so do their tangent spaces.
  exact (hdβW v w).symm.trans (hd.trans (congrArg (h * ·) (hdαW v w)))

end PartialDiffeomorph

namespace TauCeti.SmoothEmbedding

variable {E' H' Q : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'} [J.Boundaryless]
  [TopologicalSpace Q] [ChartedSpace H' Q] [IsManifold J ∞ Q] [Nonempty Q]
  [FiniteDimensional ℝ F] [K.Boundaryless] [T2Space N]
  [SecondCountableTopology M] [SecondCountableTopology N]

/-- **Contact neighbourhood germs with prescribed first-order data.** Let `i : Q → M` be a smooth
embedding of a nonempty manifold and `g : Q → N` a smooth map inducing the topology of `Q`, where
`Q`, `M` and `N` are finite-dimensional, boundaryless, and `M` and `N` are Hausdorff and second
countable. Let `A q : T_{i q} M → T_{g q} N` be linear isomorphisms, smooth in tangent coordinates,
with `A q ∘ d i_q = d g_q`. Let the one-form `α` be contact along `i(Q)` and let `c` be a positive
function on `Q` such that `β(A q v) = c q α(v)` for every tangent vector `v` at `i q`, and
`dβ(A q v, A q w) = c q dα(v, w)` for `v` and `w` in `ker α_{i q}`. Then there is a partial
diffeomorphism `φ` from `M` to `N` whose source contains `i(Q)`, with `φ ∘ i = g`, which pulls `β`
back to a positive multiple of `α` at every point of its source. No compactness is needed. -/
theorem exists_partialDiffeomorph_comp_eq_mpullback_eq_smul (i : SmoothEmbedding J I ∞ Q M)
    {g : Q → N} (hg : ContMDiff J K ∞ g) (hgi : Topology.IsInducing g)
    {A : ∀ q, TangentSpace I (i q) →L[ℝ] TangentSpace K (g q)}
    (hA : ∀ q, ContMDiffAt J 𝓘(ℝ, E →L[ℝ] F) ∞ (inTangentCoordinates I K i g A q) q)
    (hAinv : ∀ q, (A q).IsInvertible)
    (hAi : ∀ q, (A q).comp (mfderiv J I i q) = mfderiv J K g q) {c : Q → ℝ}
    (hα : ∀ q, IsContactFormAt α.val (i q)) (hc : ∀ q, 0 < c q)
    (hAβ : ∀ q (v : TangentSpace I (i q)), β.val (g q) ![A q v] = c q * α.val (i q) ![v])
    (hAdβ : ∀ q, ∀ v ∈ RoughForm.ker α.val (i q), ∀ w ∈ RoughForm.ker α.val (i q),
      mextDeriv β.val (g q) ![A q v, A q w] = c q * mextDeriv α.val (i q) ![v, w]) :
    ∃ φ : PartialDiffeomorph I K M N ∞, range i ⊆ φ.source ∧ ⇑φ ∘ i = g ∧
      ∀ x ∈ φ.source, ∃ h : ℝ, 0 < h ∧ TauCeti.mpullback I K φ β.val x = h • α.val x := by
  -- Realize `A` as the differential of a partial diffeomorphism `Ψ`, then correct `Ψ`.
  obtain ⟨Ψ, hsrc, -, -, hval, hd⟩ := i.exists_partialDiffeomorph_mfderiv_eq hg hgi hA hAinv hAi
    isOpen_univ (subset_univ _) isOpen_univ (subset_univ _)
  obtain rfl : g = Ψ ∘ i := funext fun q ↦ (hval q).symm
  obtain rfl : A = fun q ↦ mfderiv I K Ψ (i q) := funext fun q ↦ (hd q).symm
  -- The factor `c`, read on the image of `i`.
  have hext (q : Q) : Function.extend i c 1 (i q) = c q :=
    i.isEmbedding.injective.extend_apply c 1 q
  obtain ⟨φ, hφS, hφΨ, hφ⟩ := Ψ.exists_eqOn_mpullback_eq_smul hsrc (c := Function.extend i c 1)
    (by rintro _ ⟨q, rfl⟩; exact hα q) (by rintro _ ⟨q, rfl⟩; rw [hext]; exact hc q)
    (by rintro _ ⟨q, rfl⟩ v; rw [hext]; exact hAβ q v)
    (by rintro _ ⟨q, rfl⟩ v hv w hw; rw [hext]; exact hAdβ q v hv w hw)
  exact ⟨φ, hφS, funext fun q ↦ hφΨ (mem_range_self q), hφ⟩

/-- **Contact neighbourhood germs extending a map, characterized.** Along a smooth embedding
`i : Q → M` of a nonempty manifold, with the one-form `α` contact along `i(Q)`, a map `g : Q → N`
extends to a partial diffeomorphism `φ` from a neighbourhood of `i(Q)`, `φ ∘ i = g`, pulling `β`
back to a positive multiple of `α` at every point of its source, exactly when `g` is smooth and
induces the topology of `Q`, and the differential of `g` extends along `i` to linear isomorphisms
`A q : T_{i q} M → T_{g q} N`, smooth in tangent coordinates, carrying the first-order data of `β`
to those of `α` up to a positive function `c` on `Q`: `β(A q v) = c q α(v)`, and
`dβ(A q v, A q w) = c q dα(v, w)` for `v` and `w` in `ker α_{i q}`. For such a `φ`, one may take
`A q = d φ_{i q}`. -/
theorem exists_partialDiffeomorph_comp_eq_mpullback_eq_smul_iff (i : SmoothEmbedding J I ∞ Q M)
    {g : Q → N} (hα : ∀ q, IsContactFormAt α.val (i q)) :
    (∃ φ : PartialDiffeomorph I K M N ∞, range i ⊆ φ.source ∧ ⇑φ ∘ i = g ∧
      ∀ x ∈ φ.source, ∃ h : ℝ, 0 < h ∧ TauCeti.mpullback I K φ β.val x = h • α.val x) ↔
      ContMDiff J K ∞ g ∧ Topology.IsInducing g ∧
        ∃ (A : ∀ q, TangentSpace I (i q) →L[ℝ] TangentSpace K (g q)) (c : Q → ℝ),
          (∀ q, ContMDiffAt J 𝓘(ℝ, E →L[ℝ] F) ∞ (inTangentCoordinates I K i g A q) q) ∧
          (∀ q, (A q).IsInvertible) ∧ (∀ q, (A q).comp (mfderiv J I i q) = mfderiv J K g q) ∧
          (∀ q, 0 < c q) ∧
          (∀ q (v : TangentSpace I (i q)), β.val (g q) ![A q v] = c q * α.val (i q) ![v]) ∧
          ∀ q, ∀ v ∈ RoughForm.ker α.val (i q), ∀ w ∈ RoughForm.ker α.val (i q),
            mextDeriv β.val (g q) ![A q v, A q w] = c q * mextDeriv α.val (i q) ![v, w] := by
  refine ⟨fun ⟨φ, hsrc, hφi, hφ⟩ ↦ ?_, fun ⟨hg, hgi, A, c, hA, hAinv, hAi, hc, hAβ, hAdβ⟩ ↦
    i.exists_partialDiffeomorph_comp_eq_mpullback_eq_smul hg hgi hA hAinv hAi hα hc hAβ hAdβ⟩
  subst hφi
  have hiS (q : Q) : i q ∈ φ.source := hsrc (mem_range_self q)
  -- The multiplier along `i(Q)`, and the differential of `φ` along `i(Q)` as the data `A`.
  choose c hc hcφ using fun q ↦ hφ (i q) (hiS q)
  obtain ⟨hg, hgi, hA, hAinv, hAi⟩ := (i.exists_partialDiffeomorph_mfderiv_eq_iff
    (g := φ ∘ i) (A := fun q ↦ mfderiv I K φ (i q))).1 ⟨φ, hsrc, fun _ ↦ rfl, fun _ ↦ rfl⟩
  refine ⟨hg, hgi, fun q ↦ mfderiv I K φ (i q), c, hA, hAinv, hAi, hc, fun q v ↦ ?_,
    fun q v hv w hw ↦ φ.mextDeriv_mfderiv_eq_mul_of_mpullback_eq_smul
      (fun y hy ↦ (hφ y hy).imp fun _ h ↦ h.2) (hiS q) (hα q) (hcφ q) hv hw⟩
  rw [Function.comp_apply, ← mpullback_apply_one, hcφ q, ContinuousAlternatingMap.smul_apply,
    smul_eq_mul]

end TauCeti.SmoothEmbedding
