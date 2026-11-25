/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.WeilDeligne.BaseChange
public import TauCeti.RepresentationTheory.WeilDeligne.Operations
public import TauCeti.RepresentationTheory.WeilDeligne.Restriction
public import TauCeti.RepresentationTheory.WeilDeligne.Special
public import TauCeti.RepresentationTheory.WeilDeligne.Unramified

/-!
# The inertial type of a raw Weil–Deligne parameter

For a raw Weil–Deligne parameter `(V, r, N)` (`TauCeti.WeilDeligneParameter`) for a topological
group `W` with degree `deg : W →* Multiplicative ℤ`, the **inertial type** is the restriction of
`r` to the kernel of the degree, `I = ker deg`: for the local Weil group `W_K` of a nonarchimedean
local field this is the inertia subgroup `I_K`, and the inertial type is the representation of
`I_K` underlying the parameter. It has open kernel, and the monodromy commutes with it, since the
conjugation relation `r(w) N r(w)⁻¹ = q ^ deg w • N` has factor `1` on `I`.

The inertial type is functorial in morphisms and isomorphisms of parameters, commutes with
transport, and is computed termwise on direct sums, duals, twists (by the restricted character)
and tensor products. It commutes with scalar extension, and restriction along `ι : W' →* W` with
`deg ∘ ι = f · deg'` restricts the inertial type along the induced map
`ker deg' → ker deg` (`MonoidHom.subgroupComap` after `Subgroup.inclusion`, using
`TauCeti.WeilDeligneParameter.ker_le_comap_ker_of_deg`). Unramified parameters and the
special parameters `Sp(n)` have trivial inertial type.

## Main definitions

* `TauCeti.WeilDeligneParameter.inertialType`: the restriction of `r` to `ker deg`.
* `TauCeti.WeilDeligneParameter.Hom.inertialType`, `TauCeti.WeilDeligneParameter.Iso.inertialType`:
  the induced intertwining maps and equivalences.

## Main results

* `TauCeti.WeilDeligneParameter.isOpen_ker_inertialType`: the inertial type has open kernel.
* `TauCeti.WeilDeligneParameter.inertialType_mul_N`: the monodromy commutes with the inertial type.
* `TauCeti.WeilDeligneParameter.inertialType_prod`, `inertialType_dual`, `inertialType_twist`,
  `inertialType_tensor`, `inertialType_transport`: compatibility with the operations.
* `TauCeti.WeilDeligneParameter.inertialType_baseChange`,
  `TauCeti.WeilDeligneParameter.inertialType_restrict`: compatibility with scalar extension and
  with restriction.
* `TauCeti.WeilDeligneParameter.inertialType_unramified`,
  `TauCeti.WeilDeligneParameter.inertialType_special`: unramified parameters and `Sp(n)` have
  trivial inertial type.
-/

public section

noncomputable section

namespace TauCeti

namespace WeilDeligneParameter

variable {E W V V' V'' : Type*} [Field E] [Group W] [TopologicalSpace W]
  [AddCommGroup V] [Module E V] [AddCommGroup V'] [Module E V'] [AddCommGroup V''] [Module E V'']
  {deg : W →* Multiplicative ℤ} {q : ℕ}

/-- The **inertial type** of a raw Weil–Deligne parameter: the restriction of its Weil action `r`
to the kernel of the degree, which for the local Weil group is the inertia subgroup. -/
def inertialType (D : WeilDeligneParameter E W V deg q) : Representation E deg.ker V :=
  D.r.comp deg.ker.subtype

@[simp]
theorem inertialType_apply (D : WeilDeligneParameter E W V deg q) (w : deg.ker) :
    D.inertialType w = D.r w :=
  (rfl)

/-- The inertial type has open kernel: it is the preimage of the kernel of `r`. -/
theorem isOpen_ker_inertialType (D : WeilDeligneParameter E W V deg q) :
    IsOpen (D.inertialType.ker : Set deg.ker) := by
  rw [inertialType, ← MonoidHom.comap_ker, Subgroup.coe_comap]
  exact D.isOpen_ker.preimage continuous_subtypeVal

/-- **The monodromy commutes with the inertial type**: on the kernel of the degree, the
conjugation relation has factor `q ^ 0 = 1`. -/
theorem inertialType_mul_N (D : WeilDeligneParameter E W V deg q) (w : deg.ker) :
    D.inertialType w * D.N = D.N * D.inertialType w := by
  have hw : (deg w).toAdd = 0 := by simp [MonoidHom.mem_ker.1 w.property]
  simpa [hw] using D.r_mul_N w

/-! ### Functoriality -/

/-- A morphism of parameters intertwines the inertial types. -/
def Hom.inertialType {D : WeilDeligneParameter E W V deg q}
    {D' : WeilDeligneParameter E W V' deg q} (f : Hom D D') :
    D.inertialType.IntertwiningMap D'.inertialType :=
  f.toIntertwiningMap.res deg.ker.subtype

@[simp]
theorem Hom.inertialType_apply {D : WeilDeligneParameter E W V deg q}
    {D' : WeilDeligneParameter E W V' deg q} (f : Hom D D') (v : V) :
    f.inertialType v = f v :=
  congrFun (f.toIntertwiningMap.coe_res _) v

@[simp]
theorem Hom.inertialType_id (D : WeilDeligneParameter E W V deg q) :
    (Hom.id D).inertialType = .id D.inertialType := by
  rw [Hom.inertialType, Hom.id_toIntertwiningMap]
  exact Representation.IntertwiningMap.res_id _

@[simp]
theorem Hom.inertialType_comp {D : WeilDeligneParameter E W V deg q}
    {D' : WeilDeligneParameter E W V' deg q} {D'' : WeilDeligneParameter E W V'' deg q}
    (f : Hom D' D'') (g : Hom D D') :
    (f.comp g).inertialType = f.inertialType.comp g.inertialType := by
  rw [Hom.inertialType, Hom.comp_toIntertwiningMap]
  exact Representation.IntertwiningMap.res_comp _ _ _

/-- An isomorphism of parameters gives an equivalence of inertial types. -/
def Iso.inertialType {D : WeilDeligneParameter E W V deg q}
    {D' : WeilDeligneParameter E W V' deg q} (f : Iso D D') :
    D.inertialType.Equiv D'.inertialType :=
  f.toRepresentationEquiv.res deg.ker.subtype

@[simp]
theorem Iso.inertialType_apply {D : WeilDeligneParameter E W V deg q}
    {D' : WeilDeligneParameter E W V' deg q} (f : Iso D D') (v : V) :
    f.inertialType v = f v :=
  f.toRepresentationEquiv.res_apply _ v

@[simp]
theorem Iso.inertialType_refl (D : WeilDeligneParameter E W V deg q) :
    (Iso.refl D).inertialType = .refl D.inertialType := by
  ext
  simp

@[simp]
theorem Iso.inertialType_symm {D : WeilDeligneParameter E W V deg q}
    {D' : WeilDeligneParameter E W V' deg q} (f : Iso D D') :
    f.symm.inertialType = f.inertialType.symm := by
  ext v
  exact f.inertialType.injective (by simp)

@[simp]
theorem Iso.inertialType_trans {D : WeilDeligneParameter E W V deg q}
    {D' : WeilDeligneParameter E W V' deg q} {D'' : WeilDeligneParameter E W V'' deg q}
    (f : Iso D D') (g : Iso D' D'') :
    (f.trans g).inertialType = f.inertialType.trans g.inertialType := by
  ext
  simp

/-- The inertial type of a transport is the transport of the inertial type. -/
theorem inertialType_transport (D : WeilDeligneParameter E W V deg q) (e : V ≃ₗ[E] V')
    (w : deg.ker) :
    (D.transport e).inertialType w = e.conjAlgEquiv E (D.inertialType w) :=
  D.transport_r e w

/-! ### Operations -/

variable (D : WeilDeligneParameter E W V deg q) (D' : WeilDeligneParameter E W V' deg q)

/-- The inertial type of a direct sum is the direct sum of the inertial types. -/
@[simp]
theorem inertialType_prod : (D.prod D').inertialType = D.inertialType.prod D'.inertialType := by
  simp only [inertialType, prod_r]
  exact Representation.prod_comp D.r D'.r deg.ker.subtype

/-- The inertial type of the dual is the dual of the inertial type. -/
@[simp]
theorem inertialType_dual : D.dual.inertialType = D.inertialType.dual := by
  simp only [inertialType, dual_r]
  exact (Representation.dual_comp D.r deg.ker.subtype).symm

/-- The inertial type of a twist by `χ` is the twist of the inertial type by the restriction of
`χ` to the kernel of the degree. -/
@[simp]
theorem inertialType_twist [SeparatelyContinuousMul W] (χ : W →* Eˣ)
    (hχ : IsOpen (χ.ker : Set W)) :
    (D.twist χ hχ).inertialType =
      Representation.charTwist (χ.comp deg.ker.subtype) D.inertialType := by
  simp only [inertialType, twist_r]
  exact Representation.charTwist_comp χ D.r deg.ker.subtype

/-- The inertial type of a tensor product is the tensor product of the inertial types. -/
@[simp]
theorem inertialType_tensor [SeparatelyContinuousMul W] :
    (D.tensor D').inertialType = D.inertialType.tprod D'.inertialType := by
  ext w : 1
  simp [inertialType]

/-! ### Scalar extension and restriction -/

/-- The inertial type of a scalar extension is the scalar extension of the inertial type. -/
@[simp]
theorem inertialType_baseChange (E' : Type*) [Field E'] [Algebra E E'] :
    (D.baseChange E').inertialType = Representation.baseChange E' D.inertialType := by
  ext w : 1
  simp [inertialType_apply]

section Restrict

variable {W' : Type*} [Group W'] [TopologicalSpace W'] {deg' : W' →* Multiplicative ℤ}
  {ι : W' →* W} {f : ℕ}

/-- The inertial type of a restriction along `ι` is the inertial type restricted along the induced
map `ker deg' → ker deg`. -/
@[simp]
theorem inertialType_restrict (hι : Continuous ι)
    (hf : ∀ w, (deg (ι w)).toAdd = f * (deg' w).toAdd) :
    (D.restrict ι hι f hf).inertialType =
      D.inertialType.comp
        ((ι.subgroupComap deg.ker).comp (Subgroup.inclusion (ker_le_comap_ker_of_deg hf))) := by
  ext w : 1
  simp only [inertialType_apply, MonoidHom.comp_apply, restrict_r_apply]
  rw [← Subgroup.coe_inclusion (ker_le_comap_ker_of_deg hf) w]
  -- `subgroupComap_apply_coe` is stated on `Submonoid.comap`, so `simp` and `rw` cannot use it.
  exact congrArg D.r (ι.subgroupComap_apply_coe deg.ker _).symm

end Restrict

/-! ### Examples -/

/-- **Unramified parameters have trivial inertial type**: `r(w) = A ^ deg w` is the identity on
the kernel of the degree. -/
theorem inertialType_unramified (hdeg : Continuous deg) (A : LinearMap.GeneralLinearGroup E V)
    (w : deg.ker) : (unramified q hdeg A).inertialType w = 1 := by
  simp [unramified_r, MonoidHom.mem_ker.1 w.property]

/-- **The special parameter `Sp(n)` has trivial inertial type**: the weights `ω(w) ^ i` are `1` on
the kernel of the degree. -/
theorem inertialType_special (n : ℕ) (hdeg : Continuous deg) (hq : (q : E) ≠ 0)
    (w : deg.ker) : (special (W := W) q n hdeg hq).inertialType w = 1 := by
  ext v i
  simp [special_r_apply, MonoidHom.mem_ker.1 w.property]

end WeilDeligneParameter

end TauCeti
